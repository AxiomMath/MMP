module

public import MMP.AlgebraicTopology.PoincareDuality.AlexanderSquare
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderGeneral
public import Mathlib.Algebra.FiveLemma

/-!
# Alexander duality from Poincaré duality, by the five lemma

Let `X` be a closed subset of a Hausdorff space `Y`, `U = Y - X`, with a closed neighbourhood `N`
of `X`, a proper retraction `r : N → X` and a proper deformation of `N` into `X` fixing `X` and
ending at `r`, and let `C^lf(Y) / C^lf(X) → C^lf(U)` be a quasi-isomorphism. If `c ↦ c ∩ μ` is
bijective on `Y` and `c ↦ c ∩ μ|_U` on `U` in every degree, then `c ↦ c ∩ μ`,
`H^{n-k}(Y, U) → H_k X`, is bijective: compare the cohomology sequence of the pair `(Y, U)` with
the Borel–Moore sequence of `X ⊆ Y` (Bredon VI.8, Hatcher 3.44).

## Main definitions

* `MMP.cohomologyWithSupports.deltaInt`: the coboundary `H^i U → H^{i+1}(Y, U)`,
  graded by `ℤ` (zero for `i < 0`).

## Main results

* `MMP.borelMooreHomology.bijective_dualityMap_of_bijective_capProduct`: Alexander duality
  `H^{n-k}(Y, Y - X) ≅ H_k X` from Poincaré duality on `Y` and on `Y - X`.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology

universe u

namespace MMP

open MMP

namespace cohomologyWithSupports

open MMP.cohomologyWithSupports

variable (R : Type u) [CommRing R] (Y : TopCat.{u}) (X : Set Y)

/-- The coboundary `δ : H^i(Y - X) → H^{i+1}(Y, Y - X)` of the pair, graded by `ℤ`; zero for
`i < 0`, where `H^i(Y - X) = 0`. -/
def deltaInt (i : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ↥Xᶜ) Set.univ i →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) Y X (i + 1) :=
  if h : 0 ≤ i then
    (congrIndex R Y rfl (by omega)).toLinearMap ∘ₗ delta R Y X i.toNat ∘ₗ
      (congrIndex R _ rfl (Int.toNat_of_nonneg h).symm).toLinearMap
  else 0

variable {R Y X}

/-- On a natural degree `p`, `deltaInt` is the coboundary `delta` of the pair. -/
lemma deltaInt_natCast (p : ℕ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ↥Xᶜ) Set.univ p) :
    deltaInt R Y X p x = delta R Y X p x := by
  rw [deltaInt, dif_pos (by positivity)]
  rfl

/-- Cohomology with supports vanishes in negative degrees. -/
lemma subsingleton_of_neg {Z : TopCat.{u}} {S : Set Z} {i : ℤ} (hi : i < 0) :
    Subsingleton (cohomologyWithSupports R (ModuleCat.of R R) Z S i) :=
  ModuleCat.subsingleton_of_isZero (isZero_relativeSingularCohomology_of_neg R Z Sᶜ hi)

/-- A pair of additive maps through a subsingleton group is exact. -/
lemma exact_of_subsingleton {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Subsingleton N] (f : M →+ N) (g : N →+ P) : Function.Exact f g := fun y ↦ by
  rw [Subsingleton.elim y 0]
  exact ⟨fun _ ↦ ⟨0, map_zero f⟩, fun _ ↦ map_zero g⟩

variable (R Y X)

/-- Exactness of `H^i Y → H^i(Y - X) → H^{i+1}(Y, Y - X)`, graded by `ℤ`. -/
theorem exact_restrictCompl_deltaInt (i : ℤ) :
    Function.Exact (restrictCompl R Y X i).hom (deltaInt R Y X i) := by
  rcases lt_or_ge i 0 with hi | hi
  · haveI := subsingleton_of_neg (R := R) (Z := TopCat.of ↥Xᶜ) (S := Set.univ) hi
    exact exact_of_subsingleton (restrictCompl R Y X i).hom.toAddMonoidHom
      (deltaInt R Y X i).toAddMonoidHom
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    have e : ⇑(deltaInt R Y X p) = ⇑(delta R Y X p) := funext (deltaInt_natCast p)
    rw [e]
    exact exact_restrictCompl_delta R Y X p

/-- Exactness of `H^i(Y - X) → H^{i+1}(Y, Y - X) → H^{i+1} Y`, graded by `ℤ`. -/
theorem exact_deltaInt_toCohomology (i : ℤ) :
    Function.Exact (deltaInt R Y X i) (toCohomology R (ModuleCat.of R R) Y X (i + 1)).hom := by
  rcases lt_trichotomy i (-1) with hi | rfl | hi
  · haveI := subsingleton_of_neg (R := R) (Z := Y) (S := X) (i := i + 1) (by omega)
    exact exact_of_subsingleton (deltaInt R Y X i).toAddMonoidHom
      (toCohomology R (ModuleCat.of R R) Y X (i + 1)).hom.toAddMonoidHom
  · have e : deltaInt R Y X (-1) = 0 := by rw [deltaInt, dif_neg (by omega)]
    rw [e]
    intro y
    have hinj := injective_toCohomology_zero R Y X
    refine ⟨fun hy ↦ ⟨0, ?_⟩, ?_⟩
    · exact (hinj (hy.trans (map_zero _).symm)).symm
    · rintro ⟨x, rfl⟩
      exact map_zero _
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ i by omega)
    have e : ⇑(deltaInt R Y X p) = ⇑(delta R Y X p) := funext (deltaInt_natCast p)
    rw [e]
    exact exact_delta_toCohomology R Y X p

/-- Exactness of `H^j(Y, Y - X) → H^j Y → H^j(Y - X)`, graded by `ℤ`. -/
theorem exact_toCohomology_restrictCompl_int (j : ℤ) :
    Function.Exact (toCohomology R (ModuleCat.of R R) Y X j).hom (restrictCompl R Y X j).hom := by
  rcases lt_or_ge j 0 with hj | hj
  · haveI := subsingleton_of_neg (R := R) (Z := Y) (S := Set.univ) hj
    exact exact_of_subsingleton (toCohomology R (ModuleCat.of R R) Y X j).hom.toAddMonoidHom
      (restrictCompl R Y X j).hom.toAddMonoidHom
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    exact exact_toCohomology_restrictCompl R Y X p

end cohomologyWithSupports

namespace borelMooreHomology

open MMP.borelMooreHomology

open BorelMooreCap SingularChain SingularCochain BorelMooreCross

variable {R : Type u} [CommRing R]

/-- The cap product with supports `X`, read in `H^* Y`: `c ∩ a = (c|_Y) ∩ a`. -/
lemma capProduct_toCohomology (Y : TopCat.{u}) (X : Set Y) (j : ℤ) (m : ℕ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y m) :
    capProduct R Y univ j m ((cohomologyWithSupports.toCohomology R _ Y X j).hom c) a =
      capProduct R Y X j m c a := by
  by_cases h : 0 ≤ j ∧ j ≤ m
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
    have hpm : p ≤ m := by exact_mod_cast h.2
    rw [capProduct_natCast _ _ hpm, capProduct_natCast _ _ hpm,
      cohomologyWithSupports.relativeSingularCohomologyEquiv_toCohomology]
    generalize relativeSingularCohomologyEquiv R Xᶜ p c = y
    generalize homologyEquiv R Y m a = z
    induction y using Submodule.Quotient.induction_on with | H φ => ?_
    induction z using Submodule.Quotient.induction_on with | H w => ?_
    rfl
  · rw [capProduct_of_not_le R Y _ h, capProduct_of_not_le R Y _ h]
    rfl

/-- Restriction of Borel–Moore homology to an open subset commutes with `congrDegree`. -/
lemma restrict_congrDegree {Y : TopCat.{u}} [T2Space Y] (U : TopologicalSpace.Opens Y)
    {i i' : ℤ} (h : i = i') (x : borelMooreHomology R (ModuleCat.of R R) Y i) :
    (restrict R (ModuleCat.of R R) U i').hom (congrDegree R Y h x) =
      congrDegree R (TopCat.of U) h ((restrict R (ModuleCat.of R R) U i).hom x) := by
  subst h
  rfl

/-- If `f` is bijective and `s * s = 1`, then `x ↦ s • f x` is bijective. -/
lemma bijective_zsmul {M N : Type*} [AddCommGroup M] [AddCommGroup N] {f : M → N}
    (hf : Function.Bijective f) {s : ℤ} (hs : s * s = 1) :
    Function.Bijective fun x ↦ s • f x := by
  have hss : ∀ y : N, s • s • y = y := fun y ↦ by rw [smul_smul, hs, one_smul]
  refine ⟨fun a b hab ↦ hf.1 ?_, fun y ↦ ?_⟩
  · simpa only [hss] using congrArg (s • ·) hab
  · obtain ⟨a, ha⟩ := hf.2 (s • y)
    exact ⟨a, by simp only [ha, hss]⟩

/-- The sign `-(-1) ^ k` squares to `1`. -/
lemma neg_neg_one_pow_mul_self (k : ℕ) : (-(-1 : ℤ) ^ k) * (-(-1 : ℤ) ^ k) = 1 := by
  rw [neg_mul_neg, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

section fiveLemma

variable {Y : TopCat.{u}} [T2Space Y] {X : Set Y} (hX : IsClosed X)

/-- The connecting square in `ℤ`-degrees `i + k + 1 = n`. -/
theorem connecting_capProduct_restrict_int (h : IsRelativeQuasiIso R (ModuleCat.of R R) hX)
    (hXd : HasProperNeighbourhoodDeformations X) {N : Set Y} (hN : IsClosed N)
    (hXN : X ⊆ interior N) {r : C(N, X)} (hr : IsProperMap r)
    (hrX : ∀ y : N, (y : Y) ∈ X → (r y : Y) = y) {G : C(N × unitInterval, Y)}
    (hG : IsProperMap G) (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y)
    (hG0 : ∀ y, G (y, 0) = y) (hGr : ∀ y, G (y, 1) = r y) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) Y n) (i k : ℤ) (hik : i + k + 1 = n)
    (x : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (complOpens hX)) univ i) :
    (connecting R (ModuleCat.of R R) hX h k).hom
        (congrDegree R (TopCat.of (complOpens hX)) (by omega)
          (capProduct R (TopCat.of (complOpens hX)) univ i n x
            ((restrict R (ModuleCat.of R R) (complOpens hX) n).hom μ))) =
      (-(-1 : ℤ) ^ k.toNat) • congrDegree R (TopCat.of X) (by omega)
        (capProductSupport R Y hX hXd (i + 1) n
          (cohomologyWithSupports.deltaInt R Y X i x) μ) := by
  rcases lt_or_ge i 0 with hi | hi
  · haveI := cohomologyWithSupports.subsingleton_of_neg (R := R)
      (Z := TopCat.of (complOpens hX)) (S := univ) hi
    rw [Subsingleton.elim x 0]
    erw [map_zero (cohomologyWithSupports.deltaInt R Y X i)]
    simp only [map_zero, LinearMap.zero_apply, smul_zero]
  rcases lt_or_ge k 0 with hk | hk
  · haveI : Subsingleton (borelMooreHomology R (ModuleCat.of R R) (TopCat.of X) k) :=
      ModuleCat.subsingleton_of_isZero (isZero_borelMooreHomology_of_neg R _ _ hk)
    exact Subsingleton.elim _ _
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  obtain ⟨l, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  obtain rfl : n = p + l + 1 := by omega
  erw [cohomologyWithSupports.deltaInt_natCast (R := R) (Y := Y) (X := X) p x]
  exact connecting_capProduct_restrict hX h hXd hN hXN hr hrX hG hGX hG0 hGr p l x μ

/-- **Alexander duality from Poincaré duality.** Let `X` be closed in a Hausdorff space `Y`,
`U = Y - X`, with a closed neighbourhood `N`, a proper retraction `r : N → X` and a proper
deformation of `N` into `X` fixing `X` and ending at `r`, and suppose
`C^lf(Y) / C^lf(X) → C^lf(U)` is a quasi-isomorphism. If `c ↦ c ∩ μ` is bijective on `H^* Y` and
`c ↦ c ∩ μ|_U` on `H^* U` in every degree, then `c ↦ c ∩ μ`, `H^{n-k}(Y, U) → H_k X`, is
bijective for every `k`. -/
theorem bijective_dualityMap_of_bijective_capProduct
    (h : IsRelativeQuasiIso R (ModuleCat.of R R) hX)
    (hXd : HasProperNeighbourhoodDeformations X) {N : Set Y} (hN : IsClosed N)
    (hXN : X ⊆ interior N) {r : C(N, X)} (hr : IsProperMap r)
    (hrX : ∀ y : N, (y : Y) ∈ X → (r y : Y) = y) {G : C(N × unitInterval, Y)}
    (hG : IsProperMap G) (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y)
    (hG0 : ∀ y, G (y, 0) = y) (hGr : ∀ y, G (y, 1) = r y) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) Y n)
    (hY : ∀ j : ℤ, Function.Bijective fun c ↦ capProduct R Y univ j n c μ)
    (hU : ∀ j : ℤ, Function.Bijective fun c ↦ capProduct R (TopCat.of (complOpens hX)) univ j n c
      ((restrict R (ModuleCat.of R R) (complOpens hX) n).hom μ)) (k : ℤ) :
    Function.Bijective (dualityMap R hX hXd μ k) := by
  set i : ℤ := n - k - 1 with hi
  have hik : i + k + 1 = n := by omega
  set s : ℤ := -(-1 : ℤ) ^ k.toNat
  have hs : s * s = 1 := neg_neg_one_pow_mul_self _
  set U := complOpens hX
  let i₁ := (congrDegree R Y (by omega : (n : ℤ) - i = k + 1)).toLinearMap ∘ₗ
    (capProduct R Y univ i n).flip μ
  let i₂ := (congrDegree R (TopCat.of U) (by omega : (n : ℤ) - i = k + 1)).toLinearMap ∘ₗ
    (capProduct R (TopCat.of U) univ i n).flip ((restrict R (ModuleCat.of R R) U n).hom μ)
  let i₃ := s • ((congrDegree R (TopCat.of X) (by omega : (n : ℤ) - (i + 1) = k)).toLinearMap ∘ₗ
    (capProductSupport R Y hX hXd (i + 1) n).flip μ)
  let i₄ := s • ((congrDegree R Y (by omega : (n : ℤ) - (i + 1) = k)).toLinearMap ∘ₗ
    (capProduct R Y univ (i + 1) n).flip μ)
  let i₅ := s • ((congrDegree R (TopCat.of U) (by omega : (n : ℤ) - (i + 1) = k)).toLinearMap ∘ₗ
    (capProduct R (TopCat.of U) univ (i + 1) n).flip ((restrict R (ModuleCat.of R R) U n).hom μ))
  have hb3 : Function.Bijective i₃ := by
    refine LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (cohomologyWithSupports.restrictCompl R Y X i).hom
      (cohomologyWithSupports.deltaInt R Y X i)
      (cohomologyWithSupports.toCohomology R (ModuleCat.of R R) Y X (i + 1)).hom
      (cohomologyWithSupports.restrictCompl R Y X (i + 1)).hom
      (restrict R (ModuleCat.of R R) U (k + 1)).hom (connecting R (ModuleCat.of R R) hX h k).hom
      (pushforward R (ModuleCat.of R R) (subspaceInclusion Y X)
        (isProperMap_subspaceInclusion hX) k).hom
      (restrict R (ModuleCat.of R R) U k).hom i₁ i₂ i₃ i₄ i₅ ?_ ?_ ?_ ?_
      (cohomologyWithSupports.exact_restrictCompl_deltaInt R Y X i)
      (cohomologyWithSupports.exact_deltaInt_toCohomology R Y X i)
      (cohomologyWithSupports.exact_toCohomology_restrictCompl_int R Y X (i + 1))
      (exact_restrict_connecting h k) (exact_connecting_pushforward h k)
      (exact_pushforward_restrict h k) ?_ ?_ ?_ ?_
    · ext c
      simp only [i₁, i₂, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.flip_apply]
      rw [restrict_congrDegree, restrict_capProduct_univ]
      rfl
    · ext x
      simp only [i₂, i₃, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.flip_apply, LinearMap.smul_apply]
      exact connecting_capProduct_restrict_int hX h hXd hN hXN hr hrX hG hGX hG0 hGr μ i k hik x
    · ext c
      simp only [i₃, i₄, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.flip_apply, LinearMap.smul_apply, map_zsmul]
      rw [pushforward_congrDegree, capProduct_toCohomology]
      congr 2
      exact pushforward_subsetInclusion_capProductSupport R Y hX hXd (i + 1) n c μ
    · ext c
      simp only [i₄, i₅, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.flip_apply, LinearMap.smul_apply, map_zsmul]
      rw [restrict_congrDegree, restrict_capProduct_univ]
      rfl
    · exact ((LinearEquiv.bijective _).comp (hY i)).2
    · exact (LinearEquiv.bijective _).comp (hU i)
    · exact bijective_zsmul ((LinearEquiv.bijective _).comp (hY (i + 1))) hs
    · exact (bijective_zsmul ((LinearEquiv.bijective _).comp (hU (i + 1))) hs).1
  have key : ∀ (j : ℤ) (hj : j = n - k) (e : (n : ℤ) - j = k),
      Function.Bijective (fun c ↦ s • congrDegree R (TopCat.of X) e
        (capProductSupport R Y hX hXd j n c μ)) → Function.Bijective (dualityMap R hX hXd μ k) := by
    rintro j rfl e hb
    have hb' := bijective_zsmul hb hs
    simp only [smul_smul, hs, one_smul] at hb'
    exact hb'
  exact key (i + 1) (by omega) (by omega) hb3

end fiveLemma

end borelMooreHomology

end MMP
