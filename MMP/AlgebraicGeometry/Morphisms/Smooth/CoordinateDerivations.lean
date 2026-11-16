module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Ideal.Height

/-!
# Coordinate partial derivatives are a universal basis of derivations

Let `X` be a scheme over a field `k` and `x_1, …, x_n` local coordinates on an open `U ⊆ X`
(Kollár Def. 3.73, `MMP.Resolution.IsLocalCoordinatesOn`).

* The partial derivatives `∂/∂x_i` are `k`-derivations, with `∂x_j/∂x_i = δ_ij`, and every
  `k`-derivation `δ` into a module satisfies `δ(h) = ∑_i (∂h/∂x_i) δ(x_i)`.
* `∂/∂x_i` is a section of `Der_X(U)`: a vector field on `U` acting as `∂/∂x_i` on every affine
  open `W ⊆ U`.

## Implementation notes

* As in `MMP.Foundations.Resolution.Derivative`, the statements about `Ω_{U/k}` and the partial
  derivatives are read on the affine opens `W ⊆ U`, where `Ω_{U/k}(W) = Ω_{Γ(X, W)/k}` and a
  `k`-derivation of `𝒪_W` into an `𝒪_W`-module `M` is a `k`-derivation of `Γ(X, W)` into the
  `Γ(X, W)`-module `M(W)`. The expansion is stated for an arbitrary `Γ(X, W)`-module, so it
  covers every sheaf of modules `M` on every open `V ⊆ U` by restriction to affine opens
  `W ⊆ V`. That `∂/∂x_i` is a section of `Der_X(U)` (the library's
  `Stacks.Curves.SheafDerivationOf (U.ι ≫ s_X)`) is recorded separately, as the vector field
  on `U` acting on the sections over every affine open `W ⊆ U` as `∂/∂x_i`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Def. 3.73]
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry IsLocalRing

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Resolution.Bridges

open MMP.Resolution

/-! ### Partial derivatives are derivations -/

section Derivations

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {U : X.Opens} {n : ℕ}
  {x : Fin n → Γ(X, U)}

/-- The partial derivative `∂/∂x_i` on an affine open `W ⊆ U` as a `k`-derivation of
`Γ(X, W)` (Kollár Def. 3.73): the `i`-th coordinate in the basis `dx_1, …, dx_n` of
`Ω_{Γ(X, W)/k}`, composed with `d`. -/
@[mmp "lem_mmp_foundation_coordinate_derivations_universal_basis"]
def partialDerivation (hx : IsLocalCoordinatesOn sX U x) (W : X.affineOpens) (h : W.1 ≤ U)
    (i : Fin n) :
    letI := MMP.Mori.sectionAlgebra sX W.1
    Derivation k Γ(X, W) Γ(X, W) :=
  letI := MMP.Mori.sectionAlgebra sX W.1
  ((hx.basis W h).coord i).compDer (KaehlerDifferential.D k Γ(X, W))

/-- The derivation `partialDerivation hx W h i` sends `g ∈ Γ(X, W)` to its partial derivative
`partialDerivative hx W h i g`. -/
@[mmp "lem_mmp_foundation_coordinate_derivations_universal_basis"]
theorem partialDerivation_apply (hx : IsLocalCoordinatesOn sX U x) (W : X.affineOpens)
    (h : W.1 ≤ U) (i : Fin n) (g : Γ(X, W)) :
    partialDerivation hx W h i g = partialDerivative hx W h i g :=
  rfl

/-- `∂x_j/∂x_i = δ_ij` (Kollár Def. 3.73). -/
@[mmp "lem_mmp_foundation_coordinate_derivations_universal_basis"]
theorem partialDerivative_restrictSection_coordinate (hx : IsLocalCoordinatesOn sX U x)
    (W : X.affineOpens) (h : W.1 ≤ U) (i j : Fin n) :
    partialDerivative hx W h i (restrictSection W h (x j)) = if i = j then 1 else 0 := by
  let := MMP.Mori.sectionAlgebra sX W.1
  have hb : hx.basis W h j = KaehlerDifferential.D k Γ(X, W) (restrictSection W h (x j)) :=
    (hx W h).choose_spec j
  unfold partialDerivative
  rw [← hb, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [eq_comm]

/-- **The universal expansion in coordinates** (Kollár Def. 3.73). Let `x_1, …, x_n` be local
coordinates on `U`. For every affine open `W ⊆ U`, every `Γ(X, W)`-module `M` and every
`k`-derivation `δ : Γ(X, W) → M`, `δ(h) = ∑_i (∂h/∂x_i) δ(x_i)` for every `h ∈ Γ(X, W)`. -/
@[mmp "lem_mmp_foundation_coordinate_derivations_universal_basis"]
theorem derivation_eq_sum_partialDerivative_smul (hx : IsLocalCoordinatesOn sX U x)
    (W : X.affineOpens) (h : W.1 ≤ U) :
    letI := MMP.Mori.sectionAlgebra sX W.1
    ∀ (M : Type v) [AddCommGroup M] [Module Γ(X, W) M] [Module k M]
      [IsScalarTower k Γ(X, W) M] (δ : Derivation k Γ(X, W) M) (g : Γ(X, W)),
      δ g = ∑ i, partialDerivative hx W h i g • δ (restrictSection W h (x i)) := by
  let := MMP.Mori.sectionAlgebra sX W.1
  intro M _ _ _ _ δ g
  rw [← δ.liftKaehlerDifferential_comp_D g, ← sum_partialDerivative_smul hx W h g, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D]

private theorem restrict_restrictSection' {U : X.Opens} {W' W : X.affineOpens} (hW : W.1 ≤ U)
    (h' : W'.1 ≤ W.1) (g : Γ(X, U)) :
    (X.presheaf.map (homOfLE h').op).hom (restrictSection W hW g) =
      restrictSection W' (h'.trans hW) g := by
  unfold restrictSection
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem partialDerivative_add (hx : IsLocalCoordinatesOn sX U x) (W : X.affineOpens)
    (h : W.1 ≤ U) (i : Fin n) (g g' : Γ(X, W)) :
    partialDerivative hx W h i (g + g') =
      partialDerivative hx W h i g + partialDerivative hx W h i g' := by
  let := MMP.Mori.sectionAlgebra sX W.1
  simp only [← partialDerivation_apply]
  exact map_add _ _ _

private theorem partialDerivative_zero (hx : IsLocalCoordinatesOn sX U x) (W : X.affineOpens)
    (h : W.1 ≤ U) (i : Fin n) : partialDerivative hx W h i 0 = 0 := by
  let := MMP.Mori.sectionAlgebra sX W.1
  simp only [← partialDerivation_apply]
  exact map_zero _

private theorem partialDerivative_mul (hx : IsLocalCoordinatesOn sX U x) (W : X.affineOpens)
    (h : W.1 ≤ U) (i : Fin n) (g g' : Γ(X, W)) :
    partialDerivative hx W h i (g * g') =
      g * partialDerivative hx W h i g' + g' * partialDerivative hx W h i g := by
  let := MMP.Mori.sectionAlgebra sX W.1
  simp only [← partialDerivation_apply]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

private theorem partialDerivative_algebraMap (hx : IsLocalCoordinatesOn sX U x)
    (W : X.affineOpens) (h : W.1 ≤ U) (i : Fin n) (c : k) :
    partialDerivative hx W h i
      (letI := MMP.Mori.sectionAlgebra sX W.1; algebraMap k Γ(X, W) c) = 0 := by
  let := MMP.Mori.sectionAlgebra sX W.1
  simp only [← partialDerivation_apply]
  exact Derivation.map_algebraMap _ _

private theorem exists_glued_section {Y : Scheme.{u}} {T : Type*} (P : T → Y.Opens)
    (hbasis : ∀ (W : Y.Opens) (p : Y), p ∈ W → ∃ a, P a ≤ W ∧ p ∈ P a)
    (E : ∀ a, Γ(Y, P a) →+ Γ(Y, P a))
    (hnat : ∀ a b (h : P b ≤ P a) (s : Γ(Y, P a)),
      (Y.presheaf.map (homOfLE h).op).hom (E a s) = E b ((Y.presheaf.map (homOfLE h).op).hom s))
    (W : Y.Opens) (s : Γ(Y, W)) :
    ∃ t : Γ(Y, W), ∀ a (h : P a ≤ W),
      (Y.presheaf.map (homOfLE h).op).hom t = E a ((Y.presheaf.map (homOfLE h).op).hom s) := by
  let c : ∀ i : {a : T // P a ≤ W}, Γ(Y, P i.1) := fun i =>
    E i.1 ((Y.presheaf.map (homOfLE i.2).op).hom s)
  have hcompat :
      TopCat.Presheaf.IsCompatible Y.presheaf (fun i : {a : T // P a ≤ W} => P i.1) c := by
    intro i j
    refine TopCat.Presheaf.IsSheaf.section_ext Y.sheaf.property ?_
    intro p hp
    obtain ⟨b, hb, hpb⟩ := hbasis (P i.1 ⊓ P j.1) p hp
    refine ⟨P b, hb, hpb, ?_⟩
    have h1 : P b ≤ P i.1 := hb.trans inf_le_left
    have h2 : P b ≤ P j.1 := hb.trans inf_le_right
    show (Y.presheaf.map (homOfLE hb).op).hom
        ((Y.presheaf.map (TopologicalSpace.Opens.infLELeft _ _).op).hom (c i)) =
      (Y.presheaf.map (homOfLE hb).op).hom
        ((Y.presheaf.map (TopologicalSpace.Opens.infLERight _ _).op).hom (c j))
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    have e1 : (Y.presheaf.map (homOfLE h1).op).hom (c i) =
        E b ((Y.presheaf.map (homOfLE (h1.trans i.2)).op).hom s) := by
      rw [show c i = _ from rfl, hnat i.1 b h1, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have e2 : (Y.presheaf.map (homOfLE h2).op).hom (c j) =
        E b ((Y.presheaf.map (homOfLE (h2.trans j.2)).op).hom s) := by
      rw [show c j = _ from rfl, hnat j.1 b h2, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    exact e1.trans e2.symm
  obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing' (fun i : {a : T // P a ≤ W} => P i.1) W
    (fun i => homOfLE i.2) (fun p hp => by
      obtain ⟨a, ha, hpa⟩ := hbasis W p hp
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hpa⟩) c hcompat
  exact ⟨t, fun a h => ht ⟨a, h⟩⟩

private theorem exists_glued_operator {Y : Scheme.{u}} {T : Type*} (P : T → Y.Opens)
    (hbasis : ∀ (W : Y.Opens) (p : Y), p ∈ W → ∃ a, P a ≤ W ∧ p ∈ P a)
    (E : ∀ a, Γ(Y, P a) →+ Γ(Y, P a))
    (hnat : ∀ a b (h : P b ≤ P a) (s : Γ(Y, P a)),
      (Y.presheaf.map (homOfLE h).op).hom (E a s) = E b ((Y.presheaf.map (homOfLE h).op).hom s))
    (hmul : ∀ a (s t : Γ(Y, P a)), E a (s * t) = s * E a t + t * E a s) :
    ∃ e : (W : Y.Opens) → Γ(Y, W) →+ Γ(Y, W),
      (∀ W (s t : Γ(Y, W)), e W (s * t) = s * e W t + t * e W s) ∧
      (∀ {W W' : Y.Opens} (h : W' ≤ W) (s : Γ(Y, W)),
        (Y.presheaf.map (homOfLE h).op).hom (e W s) =
          e W' ((Y.presheaf.map (homOfLE h).op).hom s)) ∧
      (∀ a (W : Y.Opens) (h : P a ≤ W) (s : Γ(Y, W)),
        (Y.presheaf.map (homOfLE h).op).hom (e W s) =
          E a ((Y.presheaf.map (homOfLE h).op).hom s)) := by
  have hext : ∀ {W : Y.Opens} (s t : Γ(Y, W)),
      (∀ a (h : P a ≤ W), (Y.presheaf.map (homOfLE h).op).hom s =
        (Y.presheaf.map (homOfLE h).op).hom t) → s = t := by
    intro W s t hst
    refine TopCat.Presheaf.IsSheaf.section_ext Y.sheaf.property ?_
    intro p hp
    obtain ⟨a, ha, hpa⟩ := hbasis W p hp
    exact ⟨P a, ha, hpa, hst a ha⟩
  choose g hg using exists_glued_section P hbasis E hnat
  have hsub : ∀ {W W' : Y.Opens} (h : W' ≤ W) (a) (h' : P a ≤ W') (s : Γ(Y, W)),
      (Y.presheaf.map (homOfLE h').op).hom ((Y.presheaf.map (homOfLE h).op).hom s) =
        (Y.presheaf.map (homOfLE (h'.trans h)).op).hom s := by
    intro W W' h a h' s
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hadd : ∀ W (s t : Γ(Y, W)), g W (s + t) = g W s + g W t := fun W s t =>
    hext _ _ fun a h => by rw [map_add, hg, hg, hg, map_add, map_add]
  have hzero : ∀ W, g W 0 = 0 := fun W =>
    hext _ _ fun a h => by rw [hg, map_zero, map_zero]
  refine ⟨fun W => { toFun := g W, map_zero' := hzero W, map_add' := hadd W }, ?_, ?_, ?_⟩
  · intro W s t
    refine hext _ _ fun a h => ?_
    show (Y.presheaf.map (homOfLE h).op).hom (g W (s * t)) = (Y.presheaf.map (homOfLE h).op).hom
      (s * g W t + t * g W s)
    rw [hg, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, hg, hg, ← hmul]
  · intro W W' h s
    refine hext _ _ fun a h' => ?_
    show (Y.presheaf.map (homOfLE h').op).hom ((Y.presheaf.map (homOfLE h).op).hom (g W s)) =
      (Y.presheaf.map (homOfLE h').op).hom (g W' ((Y.presheaf.map (homOfLE h).op).hom s))
    rw [hsub h a h', hg, hg, hsub h a h']
  · intro a W h s
    exact hg W s a h

private theorem sectionAlgebra_res' {W' W : X.Opens} (h : W' ≤ W) (c : k) :
    (X.presheaf.map (homOfLE h).op).hom
      (letI := MMP.Mori.sectionAlgebra sX W; algebraMap k Γ(X, W) c) =
      (letI := MMP.Mori.sectionAlgebra sX W'; algebraMap k Γ(X, W') c) :=
  congrArg (fun t => (((Scheme.ΓSpecIso (.of k)).inv ≫ t).hom) c)
    (Scheme.Hom.appLE_map sX (U := ⊤) (V := W) (V' := W') (by simp) (homOfLE h).op)

/-- The partial derivatives commute with restriction to smaller affine opens. -/
private theorem partialDerivative_restrict' (hx : IsLocalCoordinatesOn sX U x)
    (W W' : X.affineOpens) (h : W.1 ≤ U) (h' : W'.1 ≤ W.1) (i : Fin n) (g : Γ(X, W)) :
    (X.presheaf.map (homOfLE h').op).hom (partialDerivative hx W h i g) =
      partialDerivative hx W' (h'.trans h) i ((X.presheaf.map (homOfLE h').op).hom g) := by
  let := MMP.Mori.sectionAlgebra sX W.1
  let := MMP.Mori.sectionAlgebra sX W'.1
  let res : Γ(X, W) →+* Γ(X, W') := (X.presheaf.map (homOfLE h').op).hom
  let : Algebra Γ(X, W) Γ(X, W') := res.toAlgebra
  have : IsScalarTower k Γ(X, W) Γ(X, W') := IsScalarTower.of_algebraMap_eq fun c =>
    (sectionAlgebra_res' (sX := sX) h' c).symm
  let δ : Derivation k Γ(X, W) Γ(X, W') :=
    (partialDerivation hx W' (h'.trans h) i).compAlgebraMap Γ(X, W)
  have key := derivation_eq_sum_partialDerivative_smul hx W h Γ(X, W') δ g
  have hδ : ∀ y, δ y = partialDerivative hx W' (h'.trans h) i (res y) := fun y => rfl
  rw [hδ] at key
  rw [key, Finset.sum_eq_single i]
  · rw [hδ, restrict_restrictSection' h h' (x i), partialDerivative_restrictSection_coordinate]
    simp only [ite_true, Algebra.smul_def, mul_one]
    rfl
  · intro j _ hj
    rw [hδ, restrict_restrictSection' h h' (x j), partialDerivative_restrictSection_coordinate]
    simp [Ne.symm hj]
  · simp

private theorem iota_app_algebraMap' (sX : X ⟶ Spec (.of k)) (V : X.Opens) (W : X.Opens)
    (c : k) :
    (V.ι.app W).hom (letI := MMP.Mori.sectionAlgebra sX W; algebraMap k Γ(X, W) c) =
      (V.toScheme.presheaf.map (homOfLE (le_top : V.ι ⁻¹ᵁ W ≤ ⊤)).op).hom
        (((V.ι ≫ sX).app ⊤).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)) := by
  have h := Scheme.Hom.appLE_comp_appLE V.ι sX ⊤ W (V.ι ⁻¹ᵁ W) (by simp) le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact congrArg (fun t => ((Scheme.ΓSpecIso (.of k)).inv ≫ t).hom c) h

private theorem res_app_top_eq_iota_app_algebraMap (sX : X ⟶ Spec (.of k)) (V W : X.Opens)
    (h : V.ι ⁻¹ᵁ W ≤ (V.ι ≫ sX) ⁻¹ᵁ ⊤) (r : Γ(Spec (.of k), ⊤)) :
    (V.toScheme.presheaf.map (homOfLE h).op).hom (((V.ι ≫ sX).app ⊤).hom r) =
      (V.ι.app W).hom (letI := MMP.Mori.sectionAlgebra sX W
        algebraMap k Γ(X, W) ((Scheme.ΓSpecIso (.of k)).hom.hom r)) := by
  have hr : r = (Scheme.ΓSpecIso (.of k)).inv.hom ((Scheme.ΓSpecIso (.of k)).hom.hom r) := by
    rw [← CommRingCat.comp_apply]
    simp
  rw [iota_app_algebraMap' sX V W, ← hr]
  rfl

private theorem presheaf_map_homOfLE_refl {Y : Scheme.{u}} (W : Y.Opens) (s : Γ(Y, W)) :
    (Y.presheaf.map (homOfLE (le_refl W)).op).hom s = s := by
  rw [show (homOfLE (le_refl W)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

private theorem preimage_le_imp_le (V : X.Opens) {a b : X.Opens} (hb : b ≤ V)
    (h : V.ι ⁻¹ᵁ b ≤ V.ι ⁻¹ᵁ a) : b ≤ a := by
  intro p hpb
  exact h (show (⟨p, hb hpb⟩ : V) ∈ V.ι ⁻¹ᵁ b from hpb)

private theorem exists_affine_preimage_le (V : X.Opens) (W : V.toScheme.Opens) (p : V.toScheme)
    (hp : p ∈ W) :
    ∃ A : X.affineOpens, A.1 ≤ V ∧ V.ι ⁻¹ᵁ A.1 ≤ W ∧ p ∈ V.ι ⁻¹ᵁ A.1 := by
  have hpW : V.ι p ∈ V.ι ''ᵁ W := ⟨p, hp, rfl⟩
  obtain ⟨A, hA, hpA, hAW⟩ := exists_isAffineOpen_mem_and_subset hpW
  refine ⟨⟨A, hA⟩, ?_, ?_, hpA⟩
  · intro q hq
    obtain ⟨q', -, rfl⟩ := hAW hq
    exact q'.2
  · intro q hq
    obtain ⟨q', hq', hqq⟩ := hAW hq
    exact V.ι.isOpenEmbedding.injective hqq ▸ hq'

private theorem iota_app_naturality (V : X.Opens) {a b : X.Opens} (h : b ≤ a) (g : Γ(X, a)) :
    (V.toScheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono V.ι h) :
      V.ι ⁻¹ᵁ b ⟶ V.ι ⁻¹ᵁ a).op).hom ((V.ι.app a).hom g) =
      (V.ι.app b).hom ((X.presheaf.map (homOfLE h).op).hom g) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  exact congrArg (fun t => t.hom g) (V.ι.naturality (homOfLE h).op).symm

/-- **The partial derivatives are vector fields on `U`** (Kollár Def. 3.73): for local
coordinates `x_1, …, x_n` on `U` and each `i`, there is a `k`-derivation `∂/∂x_i ∈ Der_X(U)` of
`𝒪_U` whose action on the sections over every affine open `W ⊆ U` is the partial derivative
`∂/∂x_i` of `MMP.Resolution.partialDerivative`. -/
@[mmp "lem_mmp_foundation_coordinate_derivations_universal_basis"]
theorem exists_sheafDerivationOf_onSections_eq_partialDerivative
    (hx : IsLocalCoordinatesOn sX U x) (i : Fin n) :
    ∃ δ : Stacks.Curves.SheafDerivationOf (U.ι ≫ sX),
      ∀ (W : X.affineOpens) (h : W.1 ≤ U) (g : Γ(X, W)),
        δ.onSections ((U.ι.app W.1).hom g) =
          (U.ι.app W.1).hom (partialDerivative hx W h i g) := by
  classical
  let T := {W : X.affineOpens // W.1 ≤ U}
  let P : T → U.toScheme.Opens := fun a => U.ι ⁻¹ᵁ a.1.1
  have hbasis :
      ∀ (W : U.toScheme.Opens) (p : U.toScheme), p ∈ W → ∃ a : T, P a ≤ W ∧ p ∈ P a :=
    fun W p hp => (exists_affine_preimage_le U W p hp).elim fun A ⟨hAU, hAW, hpA⟩ =>
      ⟨⟨A, hAU⟩, hAW, hpA⟩
  let eqv : ∀ a : T, Γ(X, a.1.1) ≃+* Γ(U.toScheme, P a) := fun a =>
    have := Scheme.Hom.isIso_app U.ι a.1.1 (by simpa using a.2)
    RingEquiv.ofBijective (U.ι.app a.1.1).hom (ConcreteCategory.bijective_of_isIso _)
  have heqv : ∀ (a : T) g, eqv a g = (U.ι.app a.1.1).hom g := fun _ _ => rfl
  let E : ∀ a : T, Γ(U.toScheme, P a) →+ Γ(U.toScheme, P a) := fun a =>
    { toFun := fun s => (U.ι.app a.1.1).hom (partialDerivative hx a.1 a.2 i ((eqv a).symm s))
      map_zero' := by rw [map_zero, partialDerivative_zero, map_zero]
      map_add' := fun s t => by rw [map_add, partialDerivative_add, map_add] }
  have hE : ∀ (a : T) g, E a ((U.ι.app a.1.1).hom g) =
      (U.ι.app a.1.1).hom (partialDerivative hx a.1 a.2 i g) := by
    intro a g
    show (U.ι.app a.1.1).hom (partialDerivative hx a.1 a.2 i ((eqv a).symm ((eqv a) g))) = _
    rw [RingEquiv.symm_apply_apply]
  obtain ⟨e, hemul, hemap, hecomp⟩ := exists_glued_operator P hbasis E
    (fun a b hba s => by
      obtain ⟨g, rfl⟩ := (eqv a).surjective s
      have hba' := preimage_le_imp_le U b.2 hba
      rw [heqv, hE, iota_app_naturality U hba' (partialDerivative hx a.1 a.2 i g),
        iota_app_naturality U hba' g, hE b,
        partialDerivative_restrict' hx a.1 b.1 a.2 hba'])
    (fun a s t => by
      obtain ⟨g, rfl⟩ := (eqv a).surjective s
      obtain ⟨g', rfl⟩ := (eqv a).surjective t
      rw [← map_mul, heqv, heqv, heqv, hE, partialDerivative_mul, map_add, map_mul, map_mul, hE,
        hE])
  have hbase : ∀ (V : (Spec (.of k)).Opens) (r : Γ(Spec (.of k), V)),
      e ((U.ι ≫ sX) ⁻¹ᵁ V) (((U.ι ≫ sX).app V).hom r) = 0 := by
    intro V r
    rcases Stacks.Curves.opens_eq_bot_or_eq_top V with rfl | rfl
    · exact TopCat.Presheaf.IsSheaf.section_ext U.toScheme.sheaf.property fun p hp =>
        absurd hp (by simp)
    · refine TopCat.Presheaf.IsSheaf.section_ext U.toScheme.sheaf.property ?_
      intro p hp
      obtain ⟨a, ha, hpa⟩ := hbasis _ p hp
      refine ⟨P a, ha, hpa, ?_⟩
      show (U.toScheme.presheaf.map (homOfLE ha).op).hom (e _ (((U.ι ≫ sX).app ⊤).hom r)) =
        (U.toScheme.presheaf.map (homOfLE ha).op).hom 0
      rw [hecomp a _ ha, map_zero, res_app_top_eq_iota_app_algebraMap sX U a.1.1 ha r, hE,
        partialDerivative_algebraMap, map_zero]
  refine ⟨Stacks.Curves.sheafDerivationOfFamily (U.ι ≫ sX) e hemul
    (fun {W W'} h s => hemap h s) hbase, ?_⟩
  intro W h g
  rw [Stacks.Curves.sheafDerivationOfFamily_onSections]
  simpa only [presheaf_map_homOfLE_refl, hE] using
    hecomp ⟨W, h⟩ (P ⟨W, h⟩) le_rfl ((U.ι.app W.1).hom g)

end Derivations

end MMP.Resolution.Bridges
