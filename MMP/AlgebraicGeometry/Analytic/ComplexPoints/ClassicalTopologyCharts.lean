module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Local structure of the classical topology

Let `K` be a topological field and `X` a scheme over `K`. The classical topology on the set
`X(K)` of `K`-points (`MMP.UnderlyingSpace`) is local on `X`: for an open
immersion `j : U → X` over `K`, the induced map `U(K) → X(K)` is an open embedding with image the
set of points landing in `j(U)`; a closed immersion `i : Z → X` induces a closed embedding
`Z(K) → X(K)`, since a section of `Z` over `i⁻¹(U)` with `U` affine lifts to a section of `X`.
For `X` affine, the classical topology is the one induced by
evaluation of global sections `X(K) → K ^ Γ(X, X)`: on a basic open `D(h)` a section is a
fraction `a / hᵏ`, whose value `a(p) / h(p)ᵏ` depends continuously on the values of global
sections.

## Main results

* `MMP.UnderlyingSpace.eval_restrict`: evaluation commutes with restriction of
  sections.
* `MMP.UnderlyingSpace.isOpenEmbedding_map_of_isOpenImmersion`: an open immersion
  over `K` induces an open embedding of underlying spaces.
* `MMP.UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion`: a closed
  immersion over `K` induces a closed embedding of underlying spaces.
* `MMP.UnderlyingSpace.top_le_preimage_basicOpen_iff`: `p ∈ D(s)` iff `s(p) ≠ 0`.
* `MMP.UnderlyingSpace.isInducing_evalTop`: for `X` affine, the classical
  topology is induced by evaluation of global sections.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

namespace MMP

namespace UnderlyingSpace

variable {K : Type u} [Field K]

section Restrict

variable {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- Evaluation at `p` commutes with restriction of sections along `V' ≤ V`. -/
lemma eval_restrict {V V' : X.Opens} (h : V' ≤ V) (p : UnderlyingSpace K X)
    (hp' : ⊤ ≤ p.toHom ⁻¹ᵁ V') (g : Γ(X, V)) :
    eval p hp' (X.presheaf.map (homOfLE h).op g) =
      eval p (hp'.trans (Scheme.Hom.preimage_mono _ h)) g := by
  simp only [eval]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- The set of points of `V'(K)` at which the restriction of `g ∈ Γ(X, V)` takes a value in `W` is
the set of points of `V(K)` at which `g` takes a value in `W`, intersected with `V'(K)`. -/
lemma evalPreimage_restrict {V V' : X.Opens} (h : V' ≤ V) (g : Γ(X, V)) (W : Set K) :
    evalPreimage V' (X.presheaf.map (homOfLE h).op g) W =
      evalPreimage V g W ∩ {p | ⊤ ≤ p.toHom ⁻¹ᵁ V'} := by
  ext p
  refine ⟨fun ⟨hp', hW⟩ ↦ ⟨⟨_, by rwa [eval_restrict h p hp'] at hW⟩, hp'⟩,
    fun ⟨⟨_, hW⟩, hp'⟩ ↦ ⟨hp', by rwa [eval_restrict h p hp']⟩⟩

/-- Transporting a section along an equality `V' = V` of opens does not change the set of points
at which it takes a value in `W`. -/
lemma evalPreimage_eqToHom {V V' : X.Opens} (h : V' = V) (g : Γ(X, V)) (W : Set K) :
    evalPreimage V' (X.presheaf.map (eqToHom h).op g) W = evalPreimage V g W := by
  subst h
  simp

end Restrict

section OpenImmersion

variable {U X : Scheme.{u}} [U.Over (Spec (.of K))] [X.Over (Spec (.of K))]

/-- A monomorphism `j : U → X` over `K` induces an injective map `U(K) → X(K)`. -/
lemma mapFun_injective_of_mono (j : U ⟶ X) [Mono j] [j.IsOver (Spec (.of K))] :
    Function.Injective (mapFun (K := K) j) := fun p q h ↦
  UnderlyingSpace.ext ((cancel_mono j).mp (congrArg toHom h))

/-- The image of `U(K) → X(K)` under an open immersion `j : U → X` over `K` is the set of
`K`-points of `X` landing in `j(U)`. -/
lemma range_mapFun_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (.of K))] :
    Set.range (mapFun (K := K) j) = {p | ⊤ ≤ p.toHom ⁻¹ᵁ j.opensRange} := by
  ext p
  refine ⟨?_, fun hp ↦ ?_⟩
  · rintro ⟨q, rfl⟩ x _
    exact ⟨_, rfl⟩
  · have H : Set.range p.toHom ⊆ Set.range j := by
      rintro _ ⟨x, rfl⟩
      exact hp (Set.mem_univ x)
    refine ⟨⟨IsOpenImmersion.lift j p.toHom H, ?_⟩, ?_⟩
    · rw [← comp_over j (Spec (.of K)),
        ← Category.assoc, IsOpenImmersion.lift_fac, p.toHom_comp_over]
    · exact UnderlyingSpace.ext (IsOpenImmersion.lift_fac j p.toHom H)

variable [TopologicalSpace K]

/-- An open immersion `j : U → X` over `K` induces an inducing map `U(K) → X(K)` of underlying
spaces. -/
lemma isInducing_map_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (.of K))] :
    IsInducing (map (K := K) j) := by
  rw [isInducing_iff]
  refine le_antisymm (continuous_iff_le_induced.mp (map j).continuous) ?_
  refine le_generateFrom ?_
  rintro _ ⟨V, g, W, hW, rfl⟩
  refine ⟨_, isOpen_evalPreimage (j ''ᵁ V) ((j.appIso V).inv g) hW, ?_⟩
  change mapFun j ⁻¹' _ = _
  rw [mapFun_preimage_evalPreimage, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_app,
    evalPreimage_eqToHom]

/-- An open immersion `j : U → X` over `K` induces an open embedding `U(K) → X(K)` of
underlying spaces. -/
theorem isOpenEmbedding_map_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (.of K))] :
    IsOpenEmbedding (map (K := K) j) := by
  refine ⟨⟨isInducing_map_of_isOpenImmersion j, mapFun_injective_of_mono j⟩, ?_⟩
  change IsOpen (Set.range (mapFun j))
  rw [range_mapFun_of_isOpenImmersion]
  exact isOpen_setOf_le_preimage _

end OpenImmersion

section Affine

variable {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- Evaluation at a point of `X(K)` lying in `U`, as a ring homomorphism `Γ(X, U) → K`. -/
def evalRingHom {U : X.Opens} (p : UnderlyingSpace K X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U) :
    Γ(X, U) →+* K :=
  (p.toHom.appLE U ⊤ hp ≫ (Scheme.ΓSpecIso (.of K)).hom).hom

/-- The ring homomorphism `evalRingHom p hp` sends `g` to its value `eval p hp g` at `p`. -/
@[simp]
lemma evalRingHom_apply {U : X.Opens} (p : UnderlyingSpace K X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U)
    (g : Γ(X, U)) : evalRingHom p hp g = eval p hp g :=
  rfl

/-- A point `p ∈ U(K)` lies in the basic open `D(s)` of `s ∈ Γ(X, U)` iff `s(p) ≠ 0`. -/
lemma top_le_preimage_basicOpen_iff {U : X.Opens} (p : UnderlyingSpace K X)
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U) (s : Γ(X, U)) :
    ⊤ ≤ p.toHom ⁻¹ᵁ X.basicOpen s ↔ eval p hp s ≠ 0 := by
  have key : ⊤ ≤ p.toHom ⁻¹ᵁ X.basicOpen s ↔
      ⊤ ≤ (Spec (.of K)).basicOpen (p.toHom.appLE U ⊤ hp s) := by
    rw [Scheme.basicOpen_appLE, top_inf_eq]
  rw [key]
  have hiff : ∀ t : Γ(Spec (.of K), ⊤), ⊤ ≤ (Spec (.of K)).basicOpen t ↔ t ≠ 0 := by
    intro t
    constructor
    · rintro h rfl
      rw [Scheme.basicOpen_zero] at h
      exact h (Set.mem_univ (IsLocalRing.closedPoint K))
    · intro ht y _
      have hne : (Spec (.of K)).basicOpen t ≠ ⊥ := (basicOpen_eq_bot_iff t).not.mpr ht
      obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
      rwa [Subsingleton.elim y x]
  rw [hiff, eval]
  exact (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.map_ne_zero_iff.symm

/-- Evaluation of global sections: the map `X(K) → K ^ Γ(X, X)`. -/
def evalTop (p : UnderlyingSpace K X) : Γ(X, ⊤) → K :=
  fun a ↦ eval (U := ⊤) p (Scheme.Hom.preimage_top _).ge a

/-- The value at `p` of a fraction `a / h ^ k` in `Γ(X, D(h))`. -/
lemma eval_mk' [IsAffine X] (h a : Γ(X, ⊤)) (k : ℕ) (p : UnderlyingSpace K X)
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ X.basicOpen h) :
    have := (isAffineOpen_top X).isLocalization_basicOpen h
    eval p hp
        (IsLocalization.mk' (M := Submonoid.powers h) Γ(X, X.basicOpen h) a ⟨h ^ k, k, rfl⟩) =
      evalTop p a / evalTop p h ^ k := by
  intro _
  have hres : ∀ b : Γ(X, ⊤), eval p hp (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen h) b) =
      evalTop p b := fun b ↦ eval_restrict (X.basicOpen_le h) p hp b
  have hh : evalTop p h ≠ 0 := by
    rw [← hres, ← top_le_preimage_basicOpen_iff p hp]
    change ⊤ ≤ p.toHom ⁻¹ᵁ X.basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)
    rw [Scheme.basicOpen_res]
    exact le_inf hp hp
  rw [eq_div_iff (pow_ne_zero _ hh), ← hres, ← hres, ← evalRingHom_apply, ← evalRingHom_apply,
    ← evalRingHom_apply, ← map_pow, ← map_mul, ← map_pow, IsLocalization.mk'_spec]

/-- Evaluation of global sections `X(K) → K ^ Γ(X, X)` is continuous. -/
lemma continuous_evalTop [TopologicalSpace K] : Continuous (evalTop (K := K) (X := X)) := by
  refine continuous_pi fun a ↦ continuous_def.mpr fun W hW ↦ ?_
  convert isOpen_evalPreimage (X := X) ⊤ a hW using 1
  ext p
  exact ⟨fun h ↦ ⟨fun _ _ ↦ Set.mem_univ _, h⟩, fun ⟨_, h⟩ ↦ h⟩

variable [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T1Space K]

/-- For `X` affine, the classical topology on `X(K)` is induced by evaluation of global
sections, `X(K) → K ^ Γ(X, X)`. -/
theorem isInducing_evalTop [IsAffine X] : IsInducing (evalTop (K := K) (X := X)) := by
  rw [isInducing_iff]
  refine le_antisymm (continuous_iff_le_induced.mp continuous_evalTop) (le_generateFrom ?_)
  rintro _ ⟨V, g, W, hW, rfl⟩
  refine (@isOpen_iff_forall_mem_open _ (induced evalTop inferInstance) _).mpr ?_
  rintro p ⟨hp, hpW⟩
  have hx : p.toHom (IsLocalRing.closedPoint K) ∈ V := hp (Set.mem_univ _)
  obtain ⟨h, hhV, hxh⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨_, hx⟩ trivial
  have := (isAffineOpen_top X).isLocalization_basicOpen h
  obtain ⟨⟨a, _, k, rfl⟩, hak⟩ := IsLocalization.mk'_surjective (Submonoid.powers h)
    (X.presheaf.map (homOfLE hhV).op g)
  have hak' :
      IsLocalization.mk' (M := Submonoid.powers h) Γ(X, X.basicOpen h) a ⟨h ^ k, k, rfl⟩ =
        X.presheaf.map (homOfLE hhV).op g := hak
  let N : Set (Γ(X, ⊤) → K) := {φ | φ h ≠ 0} ∩ (fun φ ↦ φ a / φ h ^ k) ⁻¹' W
  have hN : IsOpen N := by
    refine ContinuousOn.isOpen_inter_preimage ?_
      (isOpen_compl_singleton.preimage (continuous_apply h)) hW
    exact (continuous_apply a).continuousOn.div ((continuous_apply h).pow k).continuousOn
      fun φ hφ ↦ pow_ne_zero _ hφ
  have hmem : ∀ q : UnderlyingSpace K X, ⊤ ≤ q.toHom ⁻¹ᵁ X.basicOpen h → (hq : _) →
      evalTop q a / evalTop q h ^ k = eval (U := V) q hq g := by
    intro q hqh hq
    rw [← eval_mk' h a k q hqh, hak', eval_restrict]
  refine ⟨evalTop ⁻¹' N, ?_, isOpen_induced hN, ?_⟩
  · rintro q ⟨hqh, hqW⟩
    have hqD : ⊤ ≤ q.toHom ⁻¹ᵁ X.basicOpen h :=
      (top_le_preimage_basicOpen_iff (U := ⊤) q (fun _ _ ↦ Set.mem_univ _) h).mpr hqh
    have hqV : ⊤ ≤ q.toHom ⁻¹ᵁ V := hqD.trans (Scheme.Hom.preimage_mono _ hhV)
    exact ⟨hqV, by rwa [← hmem q hqD hqV]⟩
  · have hpD : ⊤ ≤ p.toHom ⁻¹ᵁ X.basicOpen h := fun y _ ↦ by
      rwa [Subsingleton.elim y (IsLocalRing.closedPoint K)]
    refine ⟨(top_le_preimage_basicOpen_iff (U := ⊤) p (fun _ _ ↦ Set.mem_univ _) h).mp hpD, ?_⟩
    change evalTop p a / evalTop p h ^ k ∈ W
    rwa [hmem p hpD hp]

end Affine

section ClosedImmersion

variable {Z X : Scheme.{u}} [Z.Over (Spec (.of K))] [X.Over (Spec (.of K))]

/-- A point `p ∈ X(K)` lies in `U(K)` iff the image of the unique point of `Spec K` lies in
`U`. -/
lemma top_le_preimage_iff (p : UnderlyingSpace K X) (U : X.Opens) :
    ⊤ ≤ p.toHom ⁻¹ᵁ U ↔ p.toHom (IsLocalRing.closedPoint K) ∈ U :=
  ⟨fun h ↦ h (Set.mem_univ _), fun h y _ ↦ by
    rwa [Subsingleton.elim y (IsLocalRing.closedPoint K)]⟩

/-- A `K`-point of `X` whose image lies in the image of a closed immersion `i : Z → X` factors
through `i`: its pullback along `i` is a closed subscheme of the reduced one-point scheme
`Spec K` which is non-empty, hence all of it. -/
lemma exists_comp_eq_of_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    (p : Spec (.of K) ⟶ X) (hp : p (IsLocalRing.closedPoint K) ∈ Set.range i) :
    ∃ q : Spec (.of K) ⟶ Z, q ≫ i = p := by
  obtain ⟨z, hz⟩ := hp
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := i) _ z hz.symm
  have : Surjective (Limits.pullback.fst p i) :=
    ⟨fun x ↦ ⟨w, Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.fst p i)
  exact ⟨inv (Limits.pullback.fst p i) ≫ Limits.pullback.snd p i, by
    rw [Category.assoc, ← Limits.pullback.condition, IsIso.inv_hom_id_assoc]⟩

/-- The image of `Z(K) → X(K)` under a closed immersion `i : Z → X` over `K` is the set of
`K`-points of `X` whose image lies in the image of `i`. -/
lemma range_mapFun_of_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (.of K))] :
    Set.range (mapFun (K := K) i) =
      {p | p.toHom (IsLocalRing.closedPoint K) ∈ Set.range i} := by
  ext p
  refine ⟨?_, fun hp ↦ ?_⟩
  · rintro ⟨q, rfl⟩
    exact ⟨_, rfl⟩
  · obtain ⟨q, hq⟩ := exists_comp_eq_of_isClosedImmersion i p.toHom hp
    refine ⟨⟨q, ?_⟩, UnderlyingSpace.ext hq⟩
    rw [← comp_over i (Spec (.of K)), ← Category.assoc, hq, p.toHom_comp_over]

variable [TopologicalSpace K]

/-- A closed immersion `i : Z → X` over `K` induces an inducing map `Z(K) → X(K)` of underlying
spaces. -/
lemma isInducing_map_of_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (.of K))] :
    IsInducing (map (K := K) i) := by
  rw [isInducing_iff]
  refine le_antisymm (continuous_iff_le_induced.mp (map i).continuous) (le_generateFrom ?_)
  rintro _ ⟨V, g, W, hW, rfl⟩
  refine (@isOpen_iff_forall_mem_open _ (induced (map i) inferInstance) _).mpr ?_
  rintro q ⟨hq, hqW⟩
  obtain ⟨t, ht, hti⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp V.2
  let O : X.Opens := ⟨t, ht⟩
  have hO : i ⁻¹ᵁ O = V := SetLike.coe_injective hti
  have hx : i (q.toHom (IsLocalRing.closedPoint K)) ∈ O := by
    change _ ∈ i ⁻¹ᵁ O
    rw [hO]
    exact (top_le_preimage_iff q V).mp hq
  obtain ⟨U', hU', hxU', hU'O⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : i ⁻¹ᵁ U' ≤ V := hO ▸ Scheme.Hom.preimage_mono _ hU'O
  obtain ⟨s, hs⟩ := i.app_surjective U' hU' (Z.presheaf.map (homOfLE hle).op g)
  refine ⟨mapFun i ⁻¹' evalPreimage U' s W, ?_, isOpen_induced (isOpen_evalPreimage _ _ hW), ?_⟩ <;>
    rw [mapFun_preimage_evalPreimage, hs, evalPreimage_restrict]
  exacts [Set.inter_subset_left, ⟨⟨hq, hqW⟩, (top_le_preimage_iff q _).mpr hxU'⟩]

/-- A closed immersion `i : Z → X` over `K` induces a closed embedding `Z(K) → X(K)` of
underlying spaces. -/
theorem isClosedEmbedding_map_of_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (.of K))] :
    IsClosedEmbedding (map (K := K) i) := by
  refine ⟨⟨isInducing_map_of_isClosedImmersion i, mapFun_injective_of_mono i⟩, ?_⟩
  change IsClosed (Set.range (mapFun i))
  rw [range_mapFun_of_isClosedImmersion]
  let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : {p : UnderlyingSpace K X | p.toHom (IsLocalRing.closedPoint K) ∈ Set.range i} =
      {p | ⊤ ≤ p.toHom ⁻¹ᵁ U}ᶜ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, top_le_preimage_iff]
    change _ ↔ ¬ _ ∉ Set.range i
    rw [not_not]
  rw [this]
  exact (isOpen_setOf_le_preimage U).isClosed_compl

end ClosedImmersion

end UnderlyingSpace

end MMP
