module
public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FlatTrace
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.Support
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE

/-!
# Global sections of coherent sheaves on proper schemes over a field

Let `k` be a field and `f : X ⟶ Spec k` proper. This file collects the finiteness and growth
properties of the cohomology, and in particular of the global sections, of coherent
`𝒪_X`-modules.

* Every `Hⁱ(X, F)` of a coherent `F` is finite-dimensional over `k`, and vanishes for
  `i > dim Supp F`.
* Global sections commute with an extension `K/k` of the ground field:
  `K ⊗_k H⁰(X, F) ≅ H⁰(X_K, F_K)`, for `X` quasi-compact and separated over `k` and `F`
  quasi-coherent.
* On a projective scheme over an algebraically closed field, a globally generated invertible
  sheaf has a regular global section.
* The Euler characteristic `χ(X, ℱ ⊗ L₁^{⊗ m₁} ⊗ ⋯ ⊗ L_r^{⊗ m_r})` is a rational polynomial in
  `m` of total degree at most `dim Supp ℱ` (Snapper).
* `h⁰(X, 𝒢 ⊗ ℒ^{⊗ m}) ≤ C m^d` for `m > 0`, where `d ≥ dim Supp 𝒢` and `ℒ` is invertible.
* If `X` is integral, `Γ(X, 𝒪_X)` is a finite field extension of `k`.

## Main results

* `MMP.finiteDimensional_and_isZero_cohomologyOverField_of_isProper`
* `MMP.Foundations.exists_tensor_globalSectionsOverField_equiv_baseChange`
* `MMP.Mori.exists_injective_smul_section_of_isGloballyGenerated`
* `MMP.Foundations.exists_eulerPolynomial_twistedSheaf_of_supp_le`
* `MMP.Foundations.exists_finrank_cohomologyOverField_zero_twistedSheaf_le_pow`
* `MMP.Foundations.exists_finrank_cohomologyOverField_zero_tensorPow_le_pow`
* `MMP.globalSections_isField_and_finite_of_isProper`

## Implementation notes

The `k`-vector space `Hⁱ(X, F)` is `AlgebraicGeometry.cohomologyOverField k f F i`, the right
derived functors of global sections with scalars restricted along `k ≅ Γ(Spec k, ⊤) → Γ(X, ⊤)`.
The dimension of the support is `topologicalKrullDim (SheafOfModules.supp F)`, valued in
`WithBot ℕ∞`, so that `F = 0` (empty support, dimension `⊥`) is covered.

The base change of global sections is given by an arbitrary cartesian square over
`Spec K ⟶ Spec k`, and the pullback `g^* s` of a global section is the unit of `g^* ⊣ g_*` on
sections over `⊤`, followed by restriction from `g⁻¹ ⊤` to `⊤`.

The growth bound for `h⁰` is proved for every proper scheme, by induction on the support
dimension along the dévissage of [Stacks, Tag 0BEM]: `h⁰` is left exact, so the short exact
sequences that give Snapper's polynomial also bound `h⁰`. The source reduces to the projective
case through a Chow modification, and there dominates `F ⊗ L^{⊗ n}` by an ample twist; neither
is needed here. The projective statement, with the monoidal tensor power `L^{⊗ n}`, follows from
the proper one.

The regular section of a globally generated invertible sheaf uses only that `k` is infinite:
the sections whose trivialising function on an affine open of a finite trivialising cover lies
in one of the finitely many associated primes form finitely many proper `k`-subspaces of
`H⁰(X, M)`, which do not cover it.

## References

* [Stacks Project, Tag 02O6], [Stacks Project, Tag 02UZ], [Stacks Project, Tag 02KH],
  [Stacks Project, Tag 0BEM]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §2.5,
  2.59–2.60
* [Hartshorne, *Algebraic Geometry*, II Ex. 4.5 and I Thm. 3.4][Hartshorne]
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u v

/-! ### Finiteness and vanishing of cohomology -/

namespace MMP

/-- A space whose topological Krull dimension is negative is empty. -/
private lemma isEmpty_of_topologicalKrullDim_lt_zero {T : Type*} [TopologicalSpace T]
    (h : topologicalKrullDim T < 0) : IsEmpty T :=
  ⟨fun x => h.not_ge (Order.krullDim_nonneg_iff.mpr
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩)⟩

/-- The global sections `H⁰` of a zero module vanish. -/
private lemma isZero_cohomologyOverField_zero_of_isZero (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {F : X.Modules} (hF : IsZero F) :
    IsZero (cohomologyOverField k f F 0) :=
  Functor.map_isZero _ <| ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map_isZero
    hF).of_iso ((SheafOfModules.evaluation _ _).rightDerivedZeroIsoSelf.app F)

/-- **Cohomology of a coherent module on a proper scheme over a field.** For `f : X ⟶ Spec k`
proper and `F` coherent, each `Hⁱ(X, F)` is finite-dimensional over `k`, and `Hⁱ(X, F) = 0`
for every `i > dim Supp F`. -/
@[mmp "lem_mmp_threefold_proper_hzero_finite"]
public theorem finiteDimensional_and_isZero_cohomologyOverField_of_isProper
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] :
    (∀ i : ℕ, FiniteDimensional k (cohomologyOverField k f F i)) ∧
      ∀ i : ℕ, topologicalKrullDim (SheafOfModules.supp F) < (i : WithBot ℕ∞) →
        IsZero (cohomologyOverField k f F i) := by
  refine ⟨finiteDimensional_cohomologyOverField_of_isProper k f F, fun i hi => ?_⟩
  cases i with
  | zero =>
    exact isZero_cohomologyOverField_zero_of_isZero k f
      (Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty F
        (Set.isEmpty_coe_sort.mp (isEmpty_of_topologicalKrullDim_lt_zero hi)))
  | succ n =>
    exact isZero_cohomologyOverField_of_topologicalKrullDim_supp_le k f F
      (ENat.WithBot.lt_add_one_iff.mp (by exact_mod_cast hi)) (Nat.lt_succ_self n)

end MMP

/-! ### Global sections under an extension of the ground field -/

namespace MMP.Foundations

/-- The identification `K ≅ Γ(Spec K, ⊤)` intertwines `algebraMap k K` with the map induced on
global sections by `Spec K ⟶ Spec k`. -/
private lemma ΓSpecIso_inv_algebraMap (k K : Type u) [Field k] [Field K] [Algebra k K] (r : k) :
    (Scheme.ΓSpecIso (.of K)).inv.hom (algebraMap k K r) =
      ((Spec.map (CommRingCat.ofHom (algebraMap k K))).appLE ⊤ ⊤ (by simp)).hom
        ((Scheme.ΓSpecIso (.of k)).inv.hom r) := by
  have e1 : (Spec.map (CommRingCat.ofHom (algebraMap k K))).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom (algebraMap k K))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [e1]
  have e2 := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (.of k)).inv.hom r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k K)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply,
    CommRingCat.hom_ofHom] at e2
  simpa only [Iso.hom_inv_id_apply] using (congrArg (Scheme.ΓSpecIso (.of K)).inv.hom e2).symm

/-- Transport of a tensor product along compatible ring isomorphisms `α : R ≃ A`,
`β : S ≃ B`: if the `R`-action on `M` is the `A`-action through `α`, then
`S ⊗[R] M ≃ B ⊗[A] M`, `c ⊗ m ↦ β c ⊗ m`. -/
private def tensorAddEquivOfRingEquiv {R S A B M : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra A B] [AddCommGroup M] [Module R M]
    [Module A M] (α : R ≃+* A) (β : S ≃+* B)
    (hαβ : ∀ r, β (algebraMap R S r) = algebraMap A B (α r))
    (hM : ∀ (r : R) (m : M), r • m = α r • m) :
    S ⊗[R] M ≃+ B ⊗[A] M where
  toFun := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun c => AddMonoidHom.mk' (fun m => β c ⊗ₜ[A] m)
      (fun _ _ => TensorProduct.tmul_add _ _ _))
      (fun _ _ => AddMonoidHom.ext fun _ => by simp [TensorProduct.add_tmul]))
    (fun r c m => by
      change β (r • c) ⊗ₜ[A] m = β c ⊗ₜ[A] (r • m)
      rw [Algebra.smul_def, map_mul, hαβ, ← Algebra.smul_def, TensorProduct.smul_tmul, hM])
  invFun := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun m => β.symm b ⊗ₜ[R] m)
      (fun _ _ => TensorProduct.tmul_add _ _ _))
      (fun _ _ => AddMonoidHom.ext fun _ => by simp [TensorProduct.add_tmul]))
    (fun a b m => by
      change β.symm (a • b) ⊗ₜ[R] m = β.symm b ⊗ₜ[R] (a • m)
      have h1 : β.symm (algebraMap A B a) = algebraMap R S (α.symm a) := by
        rw [RingEquiv.symm_apply_eq, hαβ, RingEquiv.apply_symm_apply]
      rw [Algebra.smul_def, map_mul, h1, ← Algebra.smul_def, TensorProduct.smul_tmul, hM,
        RingEquiv.apply_symm_apply])
  left_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => simp
    | add x y hx hy => simp_all
  right_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => simp
    | add x y hx hy => simp_all
  map_add' := map_add _

private lemma tensorAddEquivOfRingEquiv_tmul {R S A B M : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra A B] [AddCommGroup M] [Module R M]
    [Module A M] (α : R ≃+* A) (β : S ≃+* B)
    (hαβ : ∀ r, β (algebraMap R S r) = algebraMap A B (α r))
    (hM : ∀ (r : R) (m : M), r • m = α r • m) (c : S) (m : M) :
    tensorAddEquivOfRingEquiv α β hαβ hM (c ⊗ₜ m) = β c ⊗ₜ m := by
  simp [tensorAddEquivOfRingEquiv]

/-- Restriction of sections between two opens with the same points is bijective. -/
private lemma bijective_presheaf_map_homOfLE {Y : Scheme.{u}} (G : Y.Modules) {U V : Y.Opens}
    (hUV : U ≤ V) (hVU : V ≤ U) :
    Function.Bijective (G.presheaf.map (homOfLE hUV).op) := by
  have : IsIso (homOfLE hUV) := ⟨homOfLE hVU, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  exact ConcreteCategory.bijective_of_isIso _

/-- Restriction of sections is semilinear for the scalars coming from a morphism `Y ⟶ T`. -/
private lemma presheaf_map_appLE_smul {Y T : Scheme.{u}} (fK : Y ⟶ T) (G : Y.Modules)
    {U V : Y.Opens} (hUV : U ≤ V) (eV : V ≤ fK ⁻¹ᵁ ⊤) (eU : U ≤ fK ⁻¹ᵁ ⊤) (b : Γ(T, ⊤))
    (y : Γ(G, V)) :
    G.presheaf.map (homOfLE hUV).op ((fK.appLE ⊤ V eV).hom b • y) =
      (fK.appLE ⊤ U eU).hom b • G.presheaf.map (homOfLE hUV).op y := by
  rw [Scheme.Modules.map_smul]
  congr 1
  exact congrArg (fun m => m.hom b) (Scheme.Hom.appLE_map fK eV (homOfLE hUV).op)

open Stacks.AlgebraicGeometry.SectionsBaseChange in
/-- **Global sections commute with an extension of the ground field.** For `f : X ⟶ Spec k`
quasi-compact and separated, a quasi-coherent `F`, and a cartesian square
`X_K ⟶ X`, `X_K ⟶ Spec K` over `Spec K ⟶ Spec k`, there is a `K`-linear equivalence
`K ⊗_k H⁰(X, F) ≃ H⁰(X_K, g^* F)` sending `1 ⊗ s` to `g^* s`; when `f` is proper and `F`
coherent, both sides are finite-dimensional, of the same dimension. -/
@[mmp "lem_mmp_foundation_coherent_sections_field_extension"]
public theorem exists_tensor_globalSectionsOverField_equiv_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X XK : Scheme.{u}} (f : X ⟶ Spec (.of k)) (fK : XK ⟶ Spec (.of K)) (g : XK ⟶ X)
    (h : IsPullback g fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [QuasiCompact f] [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    let H : ModuleCat.{u} k :=
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).obj
        ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj F)
    let HK : ModuleCat.{u} K :=
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appLE ⊤ ⊤ (by simp)).hom).obj
        ((SheafOfModules.evaluation XK.ringCatSheaf (op ⊤)).obj ((Scheme.Modules.pullback g).obj F))
    (∃ e : K ⊗[k] H ≃ₗ[K] HK,
      ∀ s : Γ(F, ⊤),
        e (1 ⊗ₜ[k] s) = ((Scheme.Modules.pullback g).obj F).presheaf.map
          (homOfLE (show (⊤ : XK.Opens) ≤ g ⁻¹ᵁ ⊤ from le_top)).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).app ⊤) s)) ∧
      (IsProper f → F.IsCoherent →
        FiniteDimensional k H ∧ FiniteDimensional K HK ∧
          Module.finrank K HK = Module.finrank k H) := by
  intro H HK
  set q := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hflat : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom :=
    RingHom.Flat.of_isField (MulEquiv.isField (Field.toIsField k)
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv) _
  letI := baseAlgebra q
  letI := baseModule f F ⊤
  letI := baseModule (g ≫ f) ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ ⊤)
  letI := baseModule fK ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ ⊤)
  letI := baseTower h ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ ⊤)
  have hbij : Function.Bijective (sectionsBaseChangeMap h F ⊤) :=
    have := QuasiCompact.compactSpace_of_compactSpace f
    Stacks.FlatTrace.bijective_sectionsBaseChangeMap_of_isSeparated h F hflat ⊤
      (by simpa using isCompact_univ)
  letI : Module Γ(Spec (.of k), ⊤) H := baseModule f F ⊤
  let αe : k ≃+* Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let βe : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let θ : K ⊗[k] H ≃+ Γ(Spec (.of K), ⊤) ⊗[Γ(Spec (.of k), ⊤)] H :=
    tensorAddEquivOfRingEquiv αe βe (ΓSpecIso_inv_algebraMap k K) (fun _ _ => rfl)
  have hθ : ∀ (c : K) (s : H), θ (c ⊗ₜ s) = βe c ⊗ₜ s :=
    tensorAddEquivOfRingEquiv_tmul αe βe (ΓSpecIso_inv_algebraMap k K) (fun _ _ => rfl)
  let Ψ : Γ(Spec (.of K), ⊤) ⊗[Γ(Spec (.of k), ⊤)] H →+
      Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ ⊤) :=
    (sectionsBaseChangeMap h F ⊤).toAddMonoidHom
  have hΨ : ∀ (b : Γ(Spec (.of K), ⊤)) (s : H),
      Ψ (b ⊗ₜ s) = (fK.appLE ⊤ (g ⁻¹ᵁ ⊤) (le_preimage_top fK _)).hom b •
        pullbackUnitSections g F ⊤ s :=
    fun b s => sectionsBaseChangeMap_tmul h F ⊤ b s
  let ρ : Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ ⊤) →+
      Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
    (((Scheme.Modules.pullback g).obj F).presheaf.map
      (homOfLE (show (⊤ : XK.Opens) ≤ g ⁻¹ᵁ ⊤ from le_top)).op).hom
  have hρ : Function.Bijective ρ := bijective_presheaf_map_homOfLE _ _ le_top
  have hρs : ∀ (b : Γ(Spec (.of K), ⊤)) y,
      ρ ((fK.appLE ⊤ (g ⁻¹ᵁ ⊤) (le_preimage_top fK _)).hom b • y) =
        (fK.appLE ⊤ ⊤ (le_preimage_top fK _)).hom b • ρ y :=
    presheaf_map_appLE_smul fK _ _ _ _
  let Φ : K ⊗[k] H →ₗ[K] HK :=
    { toFun := ρ.comp (Ψ.comp θ.toAddMonoidHom)
      map_add' := map_add _
      map_smul' := fun c x => by
        induction x using TensorProduct.induction_on with
        | zero =>
          simp only [smul_zero, map_zero]
          change (0 : (HK : Type u)) = c • (0 : (HK : Type u))
          exact (smul_zero c).symm
        | tmul c' s =>
          simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, RingHom.id_apply,
            TensorProduct.smul_tmul', hθ, hΨ, hρs, smul_eq_mul, map_mul, mul_smul]
          rfl
        | add x y hx hy =>
          simp only [smul_add, map_add, hx, hy]
          exact (smul_add _ _ _).symm }
  let e : K ⊗[k] H ≃ₗ[K] HK := .ofBijective Φ (hρ.comp (hbij.comp θ.bijective))
  refine ⟨⟨e, fun s => ?_⟩, fun hp hc => ?_⟩
  · change ρ (Ψ (θ ((1 : K) ⊗ₜ[k] (s : (H : Type u))))) = _
    rw [hθ 1 s]
    refine (congrArg ρ (hΨ (βe 1) s)).trans ?_
    rw [map_one, map_one, one_smul]
    rfl
  · have e0 : cohomologyOverField k f F 0 ≃ₗ[k] H := ((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).mapIso
          ((SheafOfModules.evaluation X.ringCatSheaf
            (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.app F)).toLinearEquiv
    have := (MMP.finiteDimensional_and_isZero_cohomologyOverField_of_isProper k f F).1 0
    have hH : FiniteDimensional k H := Module.Finite.equiv e0
    have hHK : FiniteDimensional K HK := Module.Finite.equiv e
    exact ⟨hH, hHK, by rw [← e.finrank_eq, Module.finrank_baseChange]⟩

end MMP.Foundations

/-! ### Regular sections of globally generated invertible sheaves -/

namespace MMP.Mori

section RegularSection

open Stacks.NonvanishingOpen

variable {X : Scheme.{v}} {M : X.Modules} {V : X.Opens}

/-- Restricting twice is restricting once. -/
private lemma map_map_homOfLE {U U' U'' : X.Opens} (h₁ : U' ≤ U) (h₂ : U'' ≤ U') (h₃ : U'' ≤ U)
    (u : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op u) =
      M.presheaf.map (homOfLE h₃).op u := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The trivializing map sends `0` to `0`. -/
private lemma triv_zero (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) {W : X.Opens}
    (h : W ⟶ V) : triv t h 0 = 0 :=
  map_zero (AddMonoidHom.mk' (triv t h) (triv_add t h))

/-- The trivializing map commutes with finite sums. -/
private lemma triv_sum (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) {W : X.Opens}
    (h : W ⟶ V) {ι : Type*} (S : Finset ι) (u : ι → Γ(M, W)) :
    triv t h (∑ i ∈ S, u i) = ∑ i ∈ S, triv t h (u i) :=
  map_sum (AddMonoidHom.mk' (triv t h) (triv_add t h)) u S

/-- The image of a nonzerodivisor of `Γ(W, 𝒪_X)`, `W` affine, in a stalk at a point of `W` is a
nonzerodivisor. -/
private lemma germ_mem_nonZeroDivisors {W : X.Opens} (hW : IsAffineOpen W) {a : Γ(X, W)}
    (ha : a ∈ nonZeroDivisors Γ(X, W)) (x : X) (hx : x ∈ W) :
    (X.presheaf.germ W x hx).hom a ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hW.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.map_nonZeroDivisors_le (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _
    ⟨a, ha, rfl⟩

/-- On an affine open `W` of a trivializing open, for a prime `p` of `Γ(W, 𝒪_X)`, a globally
generated `M` has a global section whose trivializing function on `W` is not in `p`. -/
private lemma exists_triv_notMem (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V)
    (hM : MMP.Intersection.IsGloballyGenerated M) {W : X.Opens} (hW : IsAffineOpen W)
    (hWV : W ≤ V) (p : Ideal Γ(X, W)) [hp : p.IsPrime] :
    ∃ s : Γ(M, ⊤), triv t (homOfLE hWV) (M.presheaf.map (homOfLE le_top).op s) ∉ p := by
  set y : X := hW.fromSpec ⟨p, hp⟩
  have hy : y ∈ W := by
    change y ∈ (W : Set X)
    rw [← hW.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨W', hW'W, hyW', n, s, r, heq⟩ :=
    hM y trivial W hy (M.presheaf.map (homOfLE hWV).op (basis t))
  by_contra! h
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk y) p := hW.isLocalization_stalk' ⟨p, hp⟩ hy
  have hnu : ∀ i, X.presheaf.germ W y hy (triv t (homOfLE hWV)
      (M.presheaf.map (homOfLE le_top).op (s i))) ∈ IsLocalRing.maximalIdeal _ := by
    intro i
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ p _).not.mpr (not_not.mpr (h (s i)))
  have hW'V : W' ≤ V := hW'W.trans hWV
  have key := congrArg (fun u => (X.presheaf.germ W' y hyW').hom
    (triv t (homOfLE hW'V) u)) heq
  simp only at key
  rw [map_map_homOfLE hWV hW'W hW'V, triv_res_basis, map_one] at key
  have hres : ∀ i, triv t (homOfLE hW'V) (M.presheaf.map (homOfLE le_top).op (s i)) =
      X.presheaf.map (homOfLE hW'W).op
        (triv t (homOfLE hWV) (M.presheaf.map (homOfLE le_top).op (s i))) := by
    intro i
    rw [← triv_res t (homOfLE hWV) (homOfLE hW'W) (homOfLE hW'V), map_map_homOfLE]
  rw [triv_sum] at key
  simp only [triv_smul, hres, map_sum, map_mul, TopCat.Presheaf.germ_res_apply] at key
  have h1 : (1 : X.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal _ :=
    key ▸ Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hnu i)
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- If the trivializing function of `s` on an affine open `W` is a nonzerodivisor, then a section
`r` of `𝒪_X` over `U` with `r · s|_U = 0` has zero germ at every point of `U ∩ W`. -/
private lemma germ_eq_zero_of_smul_eq_zero
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) {W : X.Opens}
    (hW : IsAffineOpen W) (hWV : W ≤ V) {s : Γ(M, ⊤)}
    (hs : triv t (homOfLE hWV) (M.presheaf.map (homOfLE le_top).op s) ∈ nonZeroDivisors Γ(X, W))
    {U : X.Opens} {r : Γ(X, U)} (hr : r • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s = 0)
    (x : X) (hxU : x ∈ U) (hxW : x ∈ W) :
    (X.presheaf.germ U x hxU).hom r = 0 := by
  have hUW : U ⊓ W ≤ V := inf_le_right.trans hWV
  have hx : x ∈ U ⊓ W := ⟨hxU, hxW⟩
  have key := congrArg (fun u => (X.presheaf.germ (U ⊓ W) x hx).hom
    (triv t (homOfLE hUW) (M.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op u))) hr
  simp only [Scheme.Modules.map_smul, triv_smul, map_zero, triv_zero, map_mul] at key
  rw [map_map_homOfLE (le_top : U ≤ ⊤) inf_le_left le_top,
    ← map_map_homOfLE (le_top : W ≤ ⊤) (inf_le_right : U ⊓ W ≤ W) le_top,
    triv_res t (homOfLE hWV) (homOfLE inf_le_right) (homOfLE hUW),
    TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at key
  exact (mem_nonZeroDivisors_iff.mp (germ_mem_nonZeroDivisors hW hs x hxW)).2 _ key

/-- **Prime avoidance for trivializing functions.** Given finitely many affine opens `W i` of a
locally Noetherian scheme, each inside an open trivializing a globally generated `M`, and a
field `k` acting on `Γ(X, 𝒪_X)`, some global section of `M` has a nonzerodivisor as trivializing
function on every `W i`: the sections failing this on `W i` lie in the union of the proper
`k`-subspaces cut out by the finitely many associated primes of `Γ(W i, 𝒪_X)`. -/
private lemma exists_forall_triv_mem_nonZeroDivisors [IsLocallyNoetherian X] (k : Type*)
    [Field k] [Infinite k] (φ : k →+* Γ(X, ⊤)) (hM : MMP.Intersection.IsGloballyGenerated M)
    {ι : Type*} [Finite ι] {V W : ι → X.Opens}
    (t : ∀ i, Stacks.SheafDescent.Trivialization X.presheaf M.val (V i))
    (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V i) :
    ∃ s : Γ(M, ⊤), ∀ i, triv (t i) (homOfLE (hWV i)) (M.presheaf.map (homOfLE le_top).op s) ∈
      nonZeroDivisors Γ(X, W i) := by
  letI : Module k Γ(M, ⊤) := Module.compHom _ φ
  have (i : ι) : IsNoetherianRing Γ(X, W i) :=
    IsLocallyNoetherian.component_noetherian ⟨W i, hW i⟩
  have (i : ι) : Finite (associatedPrimes Γ(X, W i) Γ(X, W i)) :=
    (associatedPrimes.finite _ _).to_subtype
  let S : (Σ i, associatedPrimes Γ(X, W i) Γ(X, W i)) → Submodule k Γ(M, ⊤) := fun j =>
    { carrier := {s | triv (t j.1) (homOfLE (hWV j.1)) (M.presheaf.map (homOfLE le_top).op s) ∈
        j.2.1}
      add_mem' := fun ha hb => by
        simpa only [Set.mem_setOf_eq, map_add, triv_add] using add_mem ha hb
      zero_mem' := by simp [triv_zero]
      smul_mem' := fun c s hs => by
        change triv _ _ (M.presheaf.map _ (φ c • s)) ∈ (j.2.1 : Ideal _)
        rw [Scheme.Modules.map_smul, triv_smul]
        exact Ideal.mul_mem_left _ _ hs }
  obtain ⟨s, hs⟩ : ∃ s, ∀ j, s ∉ S j := by
    by_contra! h
    obtain ⟨⟨i, p, hp⟩, htop⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ (k := k) (p := S)
      (Set.eq_univ_of_forall fun s => Set.mem_iUnion.mpr (h s))
    have := (AssociatedPrimes.mem_iff.mp hp).isPrime
    obtain ⟨s, hs⟩ := exists_triv_notMem (t i) hM (hW i) (hWV i) p
    exact hs (htop ▸ Submodule.mem_top : s ∈ S ⟨i, p, hp⟩)
  refine ⟨s, fun i => by_contra fun hn => ?_⟩
  obtain ⟨p, hp, hsp⟩ := Set.mem_iUnion₂.mp <|
    (biUnion_associatedPrimes_eq_compl_nonZeroDivisors Γ(X, W i)).symm ▸ Set.mem_compl hn
  exact hs ⟨i, p, hp⟩ hsp

end RegularSection

/-- **Regular sections of globally generated line bundles.** On a projective scheme `X` over an
algebraically closed field `k` of characteristic zero, an invertible globally generated
`𝒪_X`-module `M` has a global section `s` such that multiplication by `s`,
`Γ(U, 𝒪_X) → Γ(U, M)`, `r ↦ r · s|_U`, is injective for every open `U ⊆ X`. -/
@[mmp "lem_mmp_foundation_generated_line_bundle_regular_section"]
public theorem exists_injective_smul_section_of_isGloballyGenerated (k : Type u) [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hf : IsProjective f)
    (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]
    (hM : MMP.Intersection.IsGloballyGenerated M) :
    ∃ s : Γ(M, ⊤), ∀ U : X.Opens,
      Function.Injective fun r : Γ(X, U) => r • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s := by
  have : IsProper f := hf.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 M
  choose z hz using fun x : X => Opens.mem_iSup.mp (hV ▸ Opens.mem_top x)
  choose W hWaff hxW hWV using fun x => Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (hz x)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_nhds_subcover (fun x => (W x : Set X))
    (fun x _ => (W x).isOpen.mem_nhds (hxW x))
  let t := fun x => (htriv (z x)).some
  obtain ⟨s, hs⟩ := exists_forall_triv_mem_nonZeroDivisors k
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) hM (ι := T) (fun x => t x)
    (fun x => hWaff x) (fun x => hWV x)
  refine ⟨s, fun U r₁ r₂ h12 => sub_eq_zero.mp ?_⟩
  have h0 : (r₁ - r₂) • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr h12
  refine TopCat.Presheaf.section_ext X.sheaf U _ _ fun x hxU => ?_
  obtain ⟨y, hyT, hxy⟩ := Set.mem_iUnion₂.mp (hT.2 (Set.mem_univ x))
  exact (germ_eq_zero_of_smul_eq_zero (t y) (hWaff y) (hWV y) (hs ⟨y, hyT⟩) h0 x hxU hxy).trans
    (map_zero _).symm

end MMP.Mori

/-! ### Snapper's polynomial -/

namespace MMP.Foundations

/-- **Snapper's polynomial for a coherent sheaf.** Let `X` be proper over a field `k`, let `ℱ` be
a coherent `𝒪_X`-module with `dim Supp ℱ ≤ d`, and let `L₁, …, L_r` be invertible
`𝒪_X`-modules. There is `P ∈ ℚ[t₁, …, t_r]` of total degree at most `d` such that
`χ(X, ℱ ⊗ L₁^{⊗ m₁} ⊗ ⋯ ⊗ L_r^{⊗ m_r}) = P(m₁, …, m_r)` for all `m ∈ ℤʳ`. -/
@[mmp "lem_mmp_foundation_projective_coherent_snapper"]
public theorem exists_eulerPolynomial_twistedSheaf_of_supp_le (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) {d : ℕ}
    (hd : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ d) :
    ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ d ∧
      ∀ m : Fin r → ℤ, MvPolynomial.eval (fun j => (m j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L m)
            (@twistedSheaf_isCoherent X r F L _ hF m) : ℚ) := by
  obtain ⟨P, hP, hPe⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f L F hF
  refine ⟨P, ?_, hPe⟩
  rcases hP with rfl | h
  · simp
  · exact_mod_cast h.trans hd

/-! ### Growth of the sections of invertible twists -/

section

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `h⁰` is subadditive along a short exact sequence of finite-dimensional cohomologies. -/
private theorem finrank_zero_le_add {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₂ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₃ 0)] :
    Module.finrank k (cohomologyOverField k f S.X₂ 0) ≤
      Module.finrank k (cohomologyOverField k f S.X₁ 0) +
        Module.finrank k (cohomologyOverField k f S.X₃ 0) := by
  obtain ⟨-, -, hex, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  set ψ := (cohomologyOverFieldMap k f S.g 0).hom
  have hker : Module.finrank k (LinearMap.ker ψ) ≤
      Module.finrank k (cohomologyOverField k f S.X₁ 0) :=
    (LinearMap.exact_iff.1 (hex 0)) ▸ LinearMap.finrank_range_le _
  have := LinearMap.finrank_range_add_finrank_ker ψ
  have := Submodule.finrank_le (LinearMap.range ψ)
  omega

/-- `h⁰` is monotone along a monomorphism, as the first map of a short exact sequence. -/
private theorem finrank_zero_le_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₂ 0)] :
    Module.finrank k (cohomologyOverField k f S.X₁ 0) ≤
      Module.finrank k (cohomologyOverField k f S.X₂ 0) := by
  obtain ⟨-, hinj, -, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  exact LinearMap.finrank_le_finrank_of_injective hinj

variable [IsProper f] {r : ℕ} (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

private theorem finiteDimensional_twistedSheafFunctor_obj (G : X.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (n : Fin r → ℤ) :
    FiniteDimensional k (cohomologyOverField k f ((twistedSheafFunctor L n).obj G) 0) :=
  haveI := hG
  haveI := forall_finiteDimensional_cohomologyOverField_of_isProper k f _
    (@twistedSheaf_isCoherent X r G L _ hG n) 0
  (cohomologyOverFieldIso k f (twistedSheafFunctorObjIso L n G) 0).toLinearEquiv.symm
    |>.finiteDimensional

private theorem finrank_twistedSheafFunctor_obj (G : X.Modules) (n : Fin r → ℤ) :
    Module.finrank k (cohomologyOverField k f ((twistedSheafFunctor L n).obj G) 0) =
      Module.finrank k (cohomologyOverField k f (twistedSheaf G L n) 0) :=
  finrank_cohomologyOverField_eq_of_iso k f (twistedSheafFunctorObjIso L n G) 0

/-- `h⁰` of the twists is subadditive along a short exact sequence of coherent sheaves. -/
private theorem finrank_twistedSheaf_le_add {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h1 : _root_.SheafOfModules.IsCoherent S.X₁) (h2 : _root_.SheafOfModules.IsCoherent S.X₂)
    (h3 : _root_.SheafOfModules.IsCoherent S.X₃) (n : Fin r → ℤ) :
    Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₂ L n) 0) ≤
      Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₁ L n) 0) +
        Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₃ L n) 0) := by
  simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    finrank_twistedSheafFunctor_obj] using
    @finrank_zero_le_add k _ X f _ (shortExact_map_twistedSheafFunctor L hS n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h1 n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h2 n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h3 n)

/-- `h⁰` of the twists is monotone along the first map of a short exact sequence. -/
private theorem finrank_twistedSheaf_le_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (h2 : _root_.SheafOfModules.IsCoherent S.X₂) (n : Fin r → ℤ) :
    Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₁ L n) 0) ≤
      Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₂ L n) 0) := by
  simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, finrank_twistedSheafFunctor_obj] using
    @finrank_zero_le_of_shortExact k _ X f _ (shortExact_map_twistedSheafFunctor L hS n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h2 n)

end

/-- The support dimension depends only on the support. -/
private theorem natDimSupp_congr {X : Scheme.{u}} {A B : X.Modules}
    (h : _root_.SheafOfModules.supp A = _root_.SheafOfModules.supp B) :
    natDimSupp A = natDimSupp B := by
  unfold natDimSupp
  rw [h]

/-- A sequence growing by at most `C (m+1)^e` per step is bounded by `(h 0 + C) (m+1)^(e+1)`. -/
private theorem le_mul_pow_of_succ_le (h : ℕ → ℕ) (C e : ℕ)
    (step : ∀ m, h (m + 1) ≤ h m + C * (m + 1) ^ e) :
    ∀ m, h m ≤ (h 0 + C) * (m + 1) ^ (e + 1) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hab : (m + 1) ^ e ≤ (m + 1 + 1) ^ e := Nat.pow_le_pow_left (by omega) e
    have hpow : (m + 1) ^ (e + 1) + (m + 1) ^ e ≤ (m + 1 + 1) ^ (e + 1) := by
      rw [pow_succ, pow_succ]
      nlinarith
    have hC : C * (m + 1) ^ e ≤ (h 0 + C) * (m + 1) ^ e :=
      Nat.mul_le_mul_right _ (by omega)
    calc h (m + 1) ≤ h m + C * (m + 1) ^ e := step m
      _ ≤ (h 0 + C) * (m + 1) ^ (e + 1) + (h 0 + C) * (m + 1) ^ e := by omega
      _ = (h 0 + C) * ((m + 1) ^ (e + 1) + (m + 1) ^ e) := by ring
      _ ≤ (h 0 + C) * (m + 1 + 1) ^ (e + 1) := Nat.mul_le_mul_left _ hpow

/-- The bound `h⁰(X, 𝒢 ⊗ ℒ^{⊗ m}) ≤ C (m+1)^e` for every coherent `𝒢` of support dimension at
most `e`, on every scheme proper over `k` and for every invertible `ℒ`. -/
private def SectionGrowth (k : Type u) [Field k] (e : ℕ) : Prop :=
  ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f] (L : Fin 1 → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)] (G : X.Modules),
    _root_.SheafOfModules.IsCoherent G → natDimSupp G ≤ e →
    ∃ C : ℕ, ∀ m : ℕ,
      Module.finrank k (cohomologyOverField k f (twistedSheaf G L (fun _ => (m : ℤ))) 0) ≤
        C * (m + 1) ^ e

section

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (L : Fin 1 → X.Modules) [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- At zero-dimensional support every twist is the sheaf itself, so `h⁰` is constant. -/
private theorem finrank_cohomologyOverField_twistedSheaf_eq_of_natDimSupp_eq_zero (G : X.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (h0 : natDimSupp G = 0) (m : ℕ) :
    Module.finrank k (cohomologyOverField k f (twistedSheaf G L (fun _ => (m : ℤ))) 0) =
      Module.finrank k (cohomologyOverField k f G 0) :=
  finrank_cohomologyOverField_eq_of_iso k f
    (twistedSheafIsoOfTensorInvertibleIso L G
      (fun M hM => tensorInvertibleIso_of_natDimSupp k f G hG h0 M hM) _) 0

/-- The twist by `ℒ^{⊗ (m+1)}` is the twist by `ℒ^{⊗ m}` of `𝒢 ⊗ ℒ`. -/
private noncomputable def twistedSheafSuccIso (G : X.Modules) (m : ℕ) :
    twistedSheaf G L (fun _ => ((m + 1 : ℕ) : ℤ)) ≅
      twistedSheaf ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          (X.ringCatSheaf.2)⟩).obj G).obj (L 0))) L (fun _ => (m : ℤ)) :=
  eqToIso (congrArg (twistedSheaf G L) (show (fun _ : Fin 1 => ((m + 1 : ℕ) : ℤ)) =
      Function.update (fun _ : Fin 1 => (m : ℤ)) 0 ((fun _ : Fin 1 => (m : ℤ)) 0 + 1) by
        funext j; fin_cases j; simp)) ≪≫
    twistedSheafUpdateIso G L (fun _ => (m : ℤ)) 0 ≪≫ (twistedSheafTensorIso L G _ 0).symm

/-- **The inductive step on a scheme without embedded points**, for a coherent sheaf of full
support without embedded associated points: a regular meromorphic section of `ℒ` gives two
difference sequences `0 → 𝒜 → 𝒢 → 𝒬₁ → 0`, `0 → 𝒜 → 𝒢 ⊗ ℒ → 𝒬₂ → 0` with smaller-dimensional
`𝒬ᵢ`, so `h⁰(𝒢 ⊗ ℒ^{m+1}) ≤ h⁰(𝒢 ⊗ ℒ^m) + h⁰(𝒬₂ ⊗ ℒ^m)`. -/
private theorem bound_of_supp_eq_univ (hX : HasNoEmbeddedPoints X) (e : ℕ)
    (ih : SectionGrowth k e) (G : X.Modules) (hG : _root_.SheafOfModules.IsCoherent G)
    (hG0 : natDimSupp G ≠ 0) (hGe : natDimSupp G ≤ e + 1)
    (hemb : HasNoEmbeddedAssociatedPoints G) (hsupp : _root_.SheafOfModules.supp G = Set.univ) :
    ∃ C : ℕ, ∀ m : ℕ,
      Module.finrank k (cohomologyOverField k f (twistedSheaf G L (fun _ => (m : ℤ))) 0) ≤
        C * (m + 1) ^ (e + 1) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_hasNoEmbeddedPoints X hX (L 0)
  obtain ⟨S, T, hS, hT, cS1, cS2, cS3, cT1, cT2, cT3, ⟨eS⟩, ⟨eT⟩, ⟨e01⟩, -, -, -, hT3⟩ :=
    exists_differenceSequences_of_supp_eq_univ k f (L 0) G hG hG0 hemb hsupp s hs
  obtain ⟨C₃, h₃⟩ := ih X f L T.X₃ cT3 (by omega)
  refine ⟨_, le_mul_pow_of_succ_le
    (fun m => Module.finrank k (cohomologyOverField k f (twistedSheaf G L (fun _ => (m : ℤ))) 0))
    C₃ e (fun m => ?_)⟩
  set n : Fin 1 → ℤ := fun _ => (m : ℤ)
  beta_reduce
  rw [finrank_cohomologyOverField_eq_of_iso k f
    (twistedSheafSuccIso L G m ≪≫ twistedSheafIsoOfIso L eT.symm n) 0]
  calc _ ≤ Module.finrank k (cohomologyOverField k f (twistedSheaf T.X₁ L n) 0) +
        Module.finrank k (cohomologyOverField k f (twistedSheaf T.X₃ L n) 0) :=
        finrank_twistedSheaf_le_add k f L hT cT1 cT2 cT3 n
    _ = Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₁ L n) 0) +
        Module.finrank k (cohomologyOverField k f (twistedSheaf T.X₃ L n) 0) := by
        rw [finrank_cohomologyOverField_eq_of_iso k f (twistedSheafIsoOfIso L e01.symm n) 0]
    _ ≤ Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₂ L n) 0) +
        Module.finrank k (cohomologyOverField k f (twistedSheaf T.X₃ L n) 0) :=
        Nat.add_le_add_right (finrank_twistedSheaf_le_of_shortExact k f L hS cS2 n) _
    _ = Module.finrank k (cohomologyOverField k f (twistedSheaf G L n) 0) +
        Module.finrank k (cohomologyOverField k f (twistedSheaf T.X₃ L n) 0) := by
        rw [finrank_cohomologyOverField_eq_of_iso k f (twistedSheafIsoOfIso L eS n) 0]
    _ ≤ _ := Nat.add_le_add_left (h₃ m) _

open Stacks.AlgebraicGeometry.CoherentSubquotients in
/-- **The removal of embedded associated points.** If the bound holds for every coherent
sheaf without embedded associated points and with the support of `𝒢`, it holds for `𝒢`: the
greatest coherent subsheaf with nowhere dense support has smaller support dimension and a
quotient of that kind, and `h⁰` is subadditive. -/
private theorem bound_of_removal (e : ℕ) (ih : SectionGrowth k e) (G : X.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (hG0 : natDimSupp G ≠ 0)
    (hGe : natDimSupp G ≤ e + 1)
    (hQ : ∀ Q : X.Modules, _root_.SheafOfModules.IsCoherent Q →
      HasNoEmbeddedAssociatedPoints Q →
      _root_.SheafOfModules.supp Q = _root_.SheafOfModules.supp G →
      natDimSupp Q = natDimSupp G →
      ∃ C : ℕ, ∀ m : ℕ,
        Module.finrank k (cohomologyOverField k f (twistedSheaf Q L (fun _ => (m : ℤ))) 0) ≤
          C * (m + 1) ^ (e + 1)) :
    ∃ C : ℕ, ∀ m : ℕ,
      Module.finrank k (cohomologyOverField k f (twistedSheaf G L (fun _ => (m : ℤ))) 0) ≤
        C * (m + 1) ^ (e + 1) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : AlgebraicGeometry.IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  have : G.IsCoherent := hG
  obtain ⟨K, hK, hmax⟩ := exists_greatest_isNowhereDenseCoherentSubobject G
  have hKcoh : (K : X.Modules).IsCoherent := hK.1
  have : G.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1
  have : (K : X.Modules).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (K : X.Modules)).1
  have hQqc : (cokernel K.arrow).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel K.arrow
  have hQcoh : (cokernel K.arrow).IsCoherent := isCoherent_of_epi (cokernel.π K.arrow)
  have hQsupp : _root_.SheafOfModules.supp (R := X.ringCatSheaf) (cokernel K.arrow)
      = _root_.SheafOfModules.supp (R := X.ringCatSheaf) G := supp_cokernel_eq G K hK
  obtain ⟨C₁, h₁⟩ := hQ _ hQcoh (cokernel_hasNoEmbeddedAssociatedPoints G K hK hmax) hQsupp
    (natDimSupp_congr hQsupp)
  have hKlt := natDimSupp_lt_natDimSupp_of_isNowhereDense k f G _ hKcoh
    (supp_subset_of_mono K.arrow) hK.2 hG0
  obtain ⟨C₂, h₂⟩ := ih X f L _ hKcoh (by omega)
  refine ⟨C₂ + C₁, fun m => ?_⟩
  calc _ ≤ _ := finrank_twistedSheaf_le_add k f L (ShortComplex.shortExact_mk_cokernel_π K.arrow)
        hKcoh hG hQcoh (fun _ => (m : ℤ))
    _ ≤ C₂ * (m + 1) ^ (e + 1) + C₁ * (m + 1) ^ (e + 1) :=
        add_le_add ((h₂ m).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega)
          e.le_succ))) (h₁ m)
    _ = _ := (add_mul ..).symm

end

/-- `h⁰` of the twists of a direct image along a closed immersion is computed downstairs. -/
private theorem finrank_twistedSheaf_pushforward (k : Type u) [Field k] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k)) {r : ℕ} (L : Fin r → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj (L j))]
    (N : Z.Modules) (n : Fin r → ℤ) :
    Module.finrank k
        (cohomologyOverField k f (twistedSheaf ((Scheme.Modules.pushforward i).obj N) L n) 0) =
      Module.finrank k (cohomologyOverField k (i ≫ f)
        (twistedSheaf N (fun j => (Scheme.Modules.pullback i).obj (L j)) n) 0) := by
  rw [finrank_cohomologyOverField_eq_of_iso k f (pushforwardTwistedSheafIso i L N n),
    finrank_cohomologyOverField_pushforward_of_isClosedImmersion]

/-- **The bound, by induction on the support dimension.** In the inductive step, the embedded
associated points are removed twice: once on `X`, and once on the scheme-theoretic support `Z`
of the quotient, which has no embedded points and on which the quotient has full support. -/
private theorem sectionGrowth (k : Type u) [Field k] : ∀ e : ℕ, SectionGrowth k e
  | 0 => by
    intro X f _ L _ G hG hGe
    refine ⟨Module.finrank k (cohomologyOverField k f G 0), fun m => ?_⟩
    rw [finrank_cohomologyOverField_twistedSheaf_eq_of_natDimSupp_eq_zero k f L G hG (by omega) m]
    simp
  | e + 1 => by
    intro X f _ L _ G hG hGe
    by_cases h0 : natDimSupp G = 0
    · refine ⟨Module.finrank k (cohomologyOverField k f G 0), fun m => ?_⟩
      rw [finrank_cohomologyOverField_twistedSheaf_eq_of_natDimSupp_eq_zero k f L G hG h0 m]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have ih := sectionGrowth k e
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    refine bound_of_removal k f L e ih G hG h0 hGe fun Q hQc hQemb hQsupp hQdim => ?_
    have : Q.IsCoherent := hQc
    obtain ⟨hZ, Q', hQ'c, hQ'supp, ⟨eQ⟩⟩ :=
      exists_isCoherent_pushforward_iso_of_hasNoEmbeddedAssociatedPoints Q hQemb
    haveI : ∀ j, SheafOfModules.IsInvertible
        (annihilatorIdeal Q).subscheme.presheaf (annihilatorIdeal Q).subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback (annihilatorIdeal Q).subschemeι).obj (L j)) :=
      fun j => SheafOfModules.isInvertible_pullback (annihilatorIdeal Q).subschemeι (L j)
    have hdim : natDimSupp Q' = natDimSupp G := by
      rw [← natDimSupp_pushforward_of_isClosedImmersion (annihilatorIdeal Q).subschemeι Q',
        natDimSupp_congr (_root_.SheafOfModules.supp_eq_of_iso eQ), hQdim]
    obtain ⟨C, hC⟩ := bound_of_removal k ((annihilatorIdeal Q).subschemeι ≫ f)
      (fun j => (Scheme.Modules.pullback (annihilatorIdeal Q).subschemeι).obj (L j)) e ih Q'
      hQ'c (hdim ▸ h0) (hdim ▸ hGe) fun Q'' hc hemb hsupp hdim'' =>
        bound_of_supp_eq_univ k ((annihilatorIdeal Q).subschemeι ≫ f) _ hZ e ih Q'' hc
          (hdim''.trans hdim ▸ h0) (hdim''.trans hdim ▸ hGe) hemb (hsupp.trans hQ'supp)
    refine ⟨C, fun m => ?_⟩
    rw [finrank_cohomologyOverField_eq_of_iso k f (twistedSheafIsoOfIso L eQ.symm _) 0,
      finrank_twistedSheaf_pushforward]
    exact hC m

open MonoidalCategory Stacks.Ample in
/-- The iterated tensor power `L^{⊗ n}` is the `n`-th power of `L` in the Picard sense. -/
private theorem nonempty_tensorPow_iso_tensorPowModule (Y : Scheme.{u}) (L : Y.Modules)
    [IsInvertibleModule Y L] (n : ℕ) :
    Nonempty (MMP.Intersection.Scheme.Modules.tensorPow L n ≅ tensorPowModule Y L (n : ℤ)) := by
  induction n with
  | zero =>
    have e : unitModule Y ≅ 𝟙_ Y.Modules := Iso.refl _
    exact ⟨e.symm ≪≫ (tensorPowModuleZeroIso Y L).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    refine ⟨?_ ≪≫ tensorPowModuleAddIso Y L (n : ℤ) 1 ≪≫ (eqToIso (by push_cast; rfl) :
      tensorPowModule Y L ((n : ℤ) + 1) ≅ tensorPowModule Y L ((n + 1 : ℕ) : ℤ))⟩
    exact (tensorIso e (tensorPowModuleOneIso Y L).symm :
      MMP.Intersection.Scheme.Modules.tensorPow L n ⊗ L ≅
        tensorPowModule Y L n ⊗ tensorPowModule Y L 1)

open MonoidalCategory in
/-- `F ⊗ L^{⊗ n}` is the twisted sheaf of `F` by `L` in degree `n`. -/
private theorem nonempty_tensor_tensorPow_iso_twistedSheaf {X : Scheme.{u}} (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n : ℕ) :
    Nonempty (F ⊗ MMP.Intersection.Scheme.Modules.tensorPow L n ≅
      twistedSheaf F (fun _ : Fin 1 => L) (fun _ => (n : ℤ))) := by
  obtain ⟨e⟩ := nonempty_tensorPow_iso_tensorPowModule X L n
  exact ⟨Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl F) e ≪≫
    (Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl F)
      (Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n)).symm⟩

/-- **Sections of invertible twists grow polynomially, with degree bounded by the support
dimension.** Let `X` be proper over a field `k`, `𝒢` a coherent `𝒪_X`-module with
`dim Supp 𝒢 ≤ d`, and `ℒ` an invertible `𝒪_X`-module. There is `C > 0` such that
`h⁰(X, 𝒢 ⊗ ℒ^{⊗ m}) ≤ C m^d` for every integer `m > 0`. -/
@[mmp "lem_mmp_foundation_proper_twisted_sections_growth"]
public theorem exists_finrank_cohomologyOverField_zero_twistedSheaf_le_pow (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (G : X.Modules) (hG : _root_.SheafOfModules.IsCoherent G) (d : ℕ)
    (hd : topologicalKrullDim (_root_.SheafOfModules.supp G) ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℤ, 0 < m →
      (Module.finrank k
          (cohomologyOverField k f (twistedSheaf G (fun _ : Fin 1 => L) (fun _ => m)) 0) : ℝ)
        ≤ C * (m : ℝ) ^ d := by
  have hdG : natDimSupp G ≤ d := by
    by_cases hs : _root_.SheafOfModules.supp G = ∅
    · unfold natDimSupp
      rw [(topologicalKrullDim_supp_eq_bot_iff G).2 hs]
      simp
    · rw [← coe_natDimSupp_eq k f G hs] at hd
      exact_mod_cast hd
  obtain ⟨C, hC⟩ := sectionGrowth k d X f (fun _ => L) G hG hdG
  refine ⟨C * 2 ^ d + 1, by positivity, fun m hm => ?_⟩
  lift m to ℕ using hm.le
  have hm' : (1 : ℝ) ≤ m := Nat.one_le_cast.2 (by omega)
  calc (_ : ℝ) ≤ C * ((m : ℝ) + 1) ^ d := by exact_mod_cast hC m
    _ ≤ C * (2 * (m : ℝ)) ^ d := by gcongr; linarith
    _ = C * 2 ^ d * (m : ℝ) ^ d := by ring
    _ ≤ _ := by push_cast; gcongr; linarith

open MonoidalCategory in
/-- **Polynomial growth of sections of twists.** Let `X` be projective over a field `k`, `F` a
coherent `𝒪_X`-module whose support has dimension at most `d`, and `L` an invertible
`𝒪_X`-module. Then there is `C > 0` with `h⁰(X, F ⊗ L^{⊗n}) ≤ C n^d` for every `n > 0`. -/
@[mmp "lem_mmp_foundation_projective_twisted_sections_growth"]
public theorem exists_finrank_cohomologyOverField_zero_tensorPow_le_pow {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hf : IsProjective f) (F : X.Modules)
    [F.IsCoherent] {d : ℕ} (hd : topologicalKrullDim (SheafOfModules.supp F) ≤ d)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (Module.finrank k (cohomologyOverField k f
          (F ⊗ MMP.Intersection.Scheme.Modules.tensorPow L n) 0) : ℝ) ≤ C * (n : ℝ) ^ d := by
  have : IsProper f := hf.isProper
  obtain ⟨C, hC, hb⟩ :=
    exists_finrank_cohomologyOverField_zero_twistedSheaf_le_pow k f L F ‹_› d hd
  refine ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨e⟩ := nonempty_tensor_tensorPow_iso_twistedSheaf F L n
  rw [finrank_cohomologyOverField_eq_of_iso k f e 0]
  exact_mod_cast hb n (by exact_mod_cast hn)

end MMP.Foundations

/-! ### Global functions on an integral proper scheme -/

namespace MMP

/-- Over an algebraically closed field `k`, a morphism `f : F ⟶ Spec k` whose global sections
form a domain finite over `k` along `f.appTop` induces a bijection `Γ(Spec k, ⊤) ≅ Γ(F, ⊤)`. -/
private lemma bijective_appTop_of_finite {k : Type u} [Field k] [IsAlgClosed k] {F : Scheme.{u}}
    (f : F ⟶ Spec (.of k)) [IsDomain Γ(F, ⊤)] (hf : f.appTop.hom.Finite) :
    Function.Bijective f.appTop := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have := IsAlgClosed.ringHom_bijective_of_isIntegral _
    (hf.comp (RingHom.Finite.of_surjective _ e.symm.surjective)).to_isIntegral
  rw [RingHom.coe_comp] at this
  exact (Function.Bijective.of_comp_iff _ e.symm.bijective).1 this

/-- Let `F` be an integral scheme proper over a field `k` via `f`. Then `Γ(F, ⊤)` is a field,
finite over `k` along `f.appTop`; if `k` is algebraically closed then `f.appTop` is bijective;
and if `F` is affine then `F` is a single point, with `f` an isomorphism when `k` is
algebraically closed. -/
@[mmp "lem_mmp_threefold_proper_functions_field"]
public theorem globalSections_isField_and_finite_of_isProper {k : Type u} [Field k]
    {F : Scheme.{u}} (f : F ⟶ Spec (.of k)) [IsIntegral F] [IsProper f] :
    (IsField Γ(F, ⊤) ∧ f.appTop.hom.Finite) ∧
      (IsAlgClosed k → Function.Bijective f.appTop) ∧
      (IsAffine F → Subsingleton F ∧ (IsAlgClosed k → IsIso f)) := by
  have hfield : IsField Γ(F, ⊤) := isField_of_universallyClosed k f
  have hfin : f.appTop.hom.Finite := finite_appTop_of_universallyClosed k f
  refine ⟨⟨hfield, hfin⟩, fun _ => bijective_appTop_of_finite f hfin, fun _ => ⟨?_, fun _ => ?_⟩⟩
  · letI := hfield.toField
    haveI : Subsingleton (Spec Γ(F, ⊤)) := ⟨fun p q => PrimeSpectrum.ext <| by
      haveI := p.isPrime
      haveI := q.isPrime
      rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.eq_bot_of_prime q.asIdeal]⟩
    exact F.isoSpec.hom.homeomorph.injective.subsingleton
  · have : IsIso f.appTop :=
      (ConcreteCategory.isIso_iff_bijective _).2 (bijective_appTop_of_finite f hfin)
    rw [show f = F.isoSpec.hom ≫ Spec.map f.appTop ≫ (Spec (.of k)).isoSpec.inv by
      rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
      simp]
    infer_instance

end MMP
