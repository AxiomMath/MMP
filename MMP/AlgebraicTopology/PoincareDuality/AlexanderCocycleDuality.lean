module

public import MMP.AlgebraicTopology.PoincareDuality.AlexanderOpen
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderGeneral
public import MMP.AlgebraicTopology.CapProduct.Restriction
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision

/-!
# From the cocycle model to the duality map

`PoincareAlexander.DualityAt Y n z` says that the cap product `[φ] ↦ [φ ∩ z]` of the
cocycle/cycle model (`capHomQ` with `A = ∅`) is bijective `H^p Y → H_q Y` for `p + q = n`, and
that `H^p Y = 0 = H_q Y` for `p, q > n`. This file deduces the corresponding statements for the
library's groups: for `[z] = μ`,

* `c ↦ c ∩ μ`, `H^j Y = H^j(Y, Y - Y) → H_{n-j} Y` (`borelMooreHomology.capProduct` with
  `X = univ`, whose cocycles vanish on `univᶜ`, which is `∅` only propositionally) is bijective
  for every `j : ℤ` (`bijective_capProduct_univ_of_dualityAt`);
* the same for the cap product with supports into `H_{n-j}(univ)`
  (`bijective_capProductSupport_univ_of_dualityAt`), and the duality map
  (`bijective_dualityMap_univ_of_dualityAt`).

Combined with `dualityAt_of_isFundamentalClass`, this gives Poincaré duality for a fundamental
class of a manifold (`bijective_dualityMap_univ_of_isFundamentalClass`).

## Main results

* `MMP.borelMooreHomology.bijective_pushforward_of_comp_eq_id`.
* `MMP.PoincareAlexander.bijective_capProduct_univ_of_dualityAt`.
* `MMP.PoincareAlexander.bijective_capProductSupport_univ_of_dualityAt`.
* `MMP.PoincareAlexander.bijective_dualityMap_univ_of_dualityAt`.
* `MMP.PoincareAlexander.bijective_dualityMap_univ_of_isFundamentalClass`.
-/

@[expose] public noncomputable section

open CategoryTheory Set Function

universe u v

namespace MMP

namespace borelMooreHomology

variable (R : Type u) [CommRing R]

/-- Push-forward along a homeomorphism (a proper map with a proper two-sided inverse) is
bijective. -/
lemma bijective_pushforward_of_comp_eq_id {X Y : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : IsProperMap f) (hg : IsProperMap g) (hfg : f ≫ g = 𝟙 X) (hgf : g ≫ f = 𝟙 Y) (i : ℤ) :
    Bijective (pushforward R (ModuleCat.of R R) f hf i).hom := by
  refine bijective_iff_has_inverse.2 ⟨(pushforward R (ModuleCat.of R R) g hg i).hom,
    fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [pushforward_comp_apply R f g hf hg (hfg ▸ isProperMap_id) i,
      pushforward_id_apply' R _ _ hfg]
  · rw [pushforward_comp_apply R g f hg hf (hgf ▸ isProperMap_id) i,
      pushforward_id_apply' R _ _ hgf]

/-- Push-forward along the inclusion of `univ` is bijective. -/
lemma bijective_pushforward_subsetInclusion_univ (Y : TopCat.{u}) (i : ℤ) :
    Bijective (pushforward R (ModuleCat.of R R) (subsetInclusion (univ : Set Y))
      (isProperMap_subsetInclusion isClosed_univ) i).hom := by
  let e : Y ≃ₜ (univ : Set Y) := (Homeomorph.Set.univ Y).symm
  let g : Y ⟶ TopCat.of (univ : Set Y) := TopCat.ofHom ⟨e, e.continuous⟩
  exact bijective_pushforward_of_comp_eq_id R _ g _ e.isProperMap
    (TopCat.ext fun x ↦ rfl) (TopCat.ext fun x ↦ rfl) i

end borelMooreHomology

namespace PoincareAlexander

open SingularChain SingularCochain BorelMooreCross BorelMooreCap borelMooreHomology

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- If `DualityAt Y n z` and `A = ∅`, then the cap product `c ↦ c ∩ [z]`,
`H^p(Y, A) → H_q Y`, is bijective for `p + q = n`. -/
lemma bijective_capHomQ_of_eq_empty {A : Set Y} (hA : A = ∅) {n : ℕ} {z : Cyc (R := R) Y n}
    (hz : DualityAt Y n z) (p q : ℕ) (h : p + q = n) :
    Bijective fun c ↦ capHomQ R A p q n h c (Submodule.Quotient.mk z) := by
  subst hA
  exact hz.1 p q h

/-- If `DualityAt Y n z` and `A = ∅`, then `H^p(Y, A)` is trivial for `p > n`. -/
lemma subsingleton_relCohomology_of_eq_empty {A : Set Y} (hA : A = ∅) {n : ℕ}
    {z : Cyc (R := R) Y n} (hz : DualityAt Y n z) {p : ℕ} (hp : n < p) :
    Subsingleton (relCohomology R A p) := by
  subst hA
  exact hz.2.1 p hp

/-- For `0 ≤ j ≤ n`, the cap product `c ↦ c ∩ μ`, `H^j Y → H_{n-j} Y`, is the cocycle/cycle
model cap product `capHomQ` (with `A = univᶜ`), conjugated by `relativeSingularCohomologyEquiv`
and `homologyEquiv`. -/
lemma capProduct_univ_eq {n : ℕ} (μ : borelMooreHomology R (ModuleCat.of R R) Y n) (j : ℤ)
    (h : 0 ≤ j ∧ j ≤ (n : ℤ)) :
    (fun c ↦ capProduct R Y univ j n c μ) =
      ((congrDegree R Y (by omega)).trans (homologyEquiv R Y (n - j.toNat))).symm ∘
      (fun x ↦ capHomQ R (univᶜ : Set Y) j.toNat (n - j.toNat) n (by omega) x
        (homologyEquiv R Y n μ)) ∘
      ((cohomologyWithSupports.congrIndex R Y rfl (Int.toNat_of_nonneg h.1).symm).trans
          (relativeSingularCohomologyEquiv R (univᶜ : Set Y) j.toNat)) := by
  funext c
  simp only [capProduct, h, and_self, ↓reduceDIte]
  rfl

/-- **Poincaré duality on the library's groups, from the cocycle model.** If `DualityAt Y n z`
and `[z] = μ`, then `c ↦ c ∩ μ`, `H^j Y → H_{n-j} Y`, is bijective for every `j : ℤ`. -/
theorem bijective_capProduct_univ_of_dualityAt {n : ℕ}
    {μ : borelMooreHomology R (ModuleCat.of R R) Y n} {z : Cyc (R := R) Y n}
    (hzμ : homologyEquiv R Y n μ = Submodule.Quotient.mk z) (hz : DualityAt Y n z) (j : ℤ) :
    Bijective fun c ↦ capProduct R Y univ j n c μ := by
  by_cases h : 0 ≤ j ∧ j ≤ (n : ℤ)
  · rw [capProduct_univ_eq μ j h, hzμ]
    exact (LinearEquiv.bijective _).comp ((bijective_capHomQ_of_eq_empty compl_univ hz _ _ _).comp
      (LinearEquiv.bijective _))
  · rw [not_and_or, not_le, not_le] at h
    rcases h with h | h
    · have := ModuleCat.subsingleton_of_isZero
        (cohomologyWithSupports.isZero_relativeSingularCohomology_of_neg R Y (univᶜ : Set Y) h)
      obtain ⟨q, hq⟩ : ∃ q : ℕ, (n : ℤ) - j = q := ⟨((n : ℤ) - j).toNat, by omega⟩
      have := hz.2.2 q (by omega)
      have : Subsingleton (borelMooreHomology R (ModuleCat.of R R) Y ((n : ℤ) - j)) :=
        ((congrDegree R Y hq).trans (homologyEquiv R Y q)).injective.subsingleton
      exact bijective_of_subsingleton' _
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, j = p := ⟨j.toNat, by omega⟩
      have : Subsingleton (cohomologyWithSupports R (ModuleCat.of R R) Y univ p) :=
        have := subsingleton_relCohomology_of_eq_empty (R := R) compl_univ hz (p := p)
          (by omega)
        (relativeSingularCohomologyEquiv R (univᶜ : Set Y) p).injective.subsingleton
      have := ModuleCat.subsingleton_of_isZero
        (isZero_borelMooreHomology_of_neg R (ModuleCat.of R R) Y (i := (n : ℤ) - p)
          (by omega))
      exact bijective_of_subsingleton' _

/-- **The cap product with supports `X = Y`, from the cocycle model.** If `DualityAt Y n z` and
`[z] = μ`, then `c ↦ c ∩ μ`, `H^j(Y, Y - Y) → H_{n-j}(univ)`, is bijective for every `j : ℤ`. -/
theorem bijective_capProductSupport_univ_of_dualityAt {n : ℕ}
    {μ : borelMooreHomology R (ModuleCat.of R R) Y n} {z : Cyc (R := R) Y n}
    (hzμ : homologyEquiv R Y n μ = Submodule.Quotient.mk z) (hz : DualityAt Y n z)
    (hd : HasProperNeighbourhoodDeformations (univ : Set Y)) (j : ℤ) :
    Bijective fun c ↦ capProductSupport R Y isClosed_univ hd j n c μ := by
  have h := bijective_capProduct_univ_of_dualityAt hzμ hz j
  have heq : (fun c ↦ capProduct R Y univ j n c μ) =
      (borelMooreHomology.pushforward R (ModuleCat.of R R)
        (borelMooreHomology.subsetInclusion (univ : Set Y))
        (borelMooreHomology.isProperMap_subsetInclusion isClosed_univ) (n - j)).hom ∘
        fun c ↦ capProductSupport R Y isClosed_univ hd j n c μ := by
    funext c
    exact (pushforward_subsetInclusion_capProductSupport R Y isClosed_univ hd j n c μ).symm
  rw [heq] at h
  exact (Bijective.of_comp_iff' (bijective_pushforward_subsetInclusion_univ R Y _) _).1 h

/-- **The duality map for `X = Y`, from the cocycle model.** If `DualityAt Y n z` and
`[z] = μ`, then `dualityMap R isClosed_univ hd μ k`, `c ↦ c ∩ μ`, `H^{n-k}(Y, Y - Y) → H_k(univ)`,
is bijective for every `k : ℤ`. -/
theorem bijective_dualityMap_univ_of_dualityAt {n : ℕ}
    {μ : borelMooreHomology R (ModuleCat.of R R) Y n} {z : Cyc (R := R) Y n}
    (hzμ : homologyEquiv R Y n μ = Submodule.Quotient.mk z) (hz : DualityAt Y n z)
    (hd : HasProperNeighbourhoodDeformations (univ : Set Y)) (k : ℤ) :
    Bijective (dualityMap R isClosed_univ hd μ k) :=
  (LinearEquiv.bijective _).comp (bijective_capProductSupport_univ_of_dualityAt hzμ hz hd _)

section manifold

variable {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [ChartedSpace H M]

/-- **Poincaré duality.** For a fundamental class `μ` of a Hausdorff, second countable real
`n`-manifold `M`, connected or not, `c ↦ c ∩ μ`, `H^{n-k} M → H_k(univ)` (the Borel–Moore
homology of `univ`, i.e. of `M`), is bijective for every `k : ℤ`. -/
theorem bijective_dualityMap_univ_of_isFundamentalClass {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n} (hμ : IsFundamentalClass R b μ)
    (hd : HasProperNeighbourhoodDeformations (univ : Set (TopCat.of M))) (k : ℤ) :
    Bijective (dualityMap R isClosed_univ hd μ k) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (homologyEquiv R (TopCat.of M) n μ)
  exact bijective_dualityMap_univ_of_dualityAt hz.symm
    (dualityAt_of_isFundamentalClass b μ hμ z hz.symm) hd k

end manifold

end PoincareAlexander

end MMP
