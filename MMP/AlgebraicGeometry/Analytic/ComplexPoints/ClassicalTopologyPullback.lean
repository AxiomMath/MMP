module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The classical topology on a fibre product

Let `K` be a topological field and `P = A ×_S B` a fibre product of schemes over `K`. The map
`P(K) → A(K) × B(K)`, `w ↦ (pr₁ w, pr₂ w)`, is a topological embedding. Near a point `w`, choose
affine opens `U_S ∋ w`, `U_A ⊆ f⁻¹ U_S` and `U_B ⊆ g⁻¹ U_S` around its images; then
`U_P = pr₁⁻¹ U_A ∩ pr₂⁻¹ U_B` is affine with coordinate ring
`Γ(A, U_A) ⊗_{Γ(S, U_S)} Γ(B, U_B)`, so the value at `w'` of a section over `U_P` is a polynomial
expression in values at `pr₁ w'` and `pr₂ w'` of sections of `A` and `B`, and depends
continuously on `(pr₁ w', pr₂ w')`. A section over a basic open `D(h) ⊆ U_P` is a fraction
`c / hᵏ`, which is handled the same way.

## Main results

* `MMP.UnderlyingSpace.eval_appLE`: values of pulled-back sections.
* `MMP.UnderlyingSpace.isEmbedding_prodMap_of_isPullback`: for a pullback square
  over `K`, `P(K) → A(K) × B(K)` is an embedding.
* `MMP.UnderlyingSpace.range_prodMap_of_isPullback`: its image is the set of pairs
  with the same image in `S(K)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

namespace MMP

namespace UnderlyingSpace

variable {K : Type u} [Field K]

section Eval

variable {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]

/-- The value at `p` of the pull-back `φ^* a` of a section `a` is the value of `a` at `φ(p)`. -/
lemma eval_appLE (φ : X ⟶ Y) [φ.IsOver (Spec (.of K))] {U : Y.Opens} {V : X.Opens}
    (e : V ≤ φ ⁻¹ᵁ U) (p : UnderlyingSpace K X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ V) (a : Γ(Y, U)) :
    eval p hp (φ.appLE U V e a) =
      eval (mapFun φ p) (hp.trans (Scheme.Hom.preimage_mono _ e)) a := by
  simp only [eval]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rfl

/-- The value at `p` of a fraction `a / hᵏ ∈ Γ(X, D(h))`, for `h, a` sections over an affine
open `U`. -/
lemma eval_mk'_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U) (h a : Γ(X, U)) (k : ℕ)
    (p : UnderlyingSpace K X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ X.basicOpen h) :
    have := hU.isLocalization_basicOpen h
    eval p hp (IsLocalization.mk' (M := Submonoid.powers h) Γ(X, X.basicOpen h) a
        ⟨h ^ k, k, rfl⟩) =
      eval p (hp.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le h))) a /
        eval p (hp.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le h))) h ^ k := by
  intro _
  have hres : ∀ b : Γ(X, U), eval p hp (algebraMap Γ(X, U) Γ(X, X.basicOpen h) b) =
      eval p (hp.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le h))) b :=
    fun b ↦ eval_restrict (X.basicOpen_le h) p hp b
  have hh : eval p (hp.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le h))) h ≠ 0 := by
    rw [← top_le_preimage_basicOpen_iff]
    exact hp
  rw [eq_div_iff (pow_ne_zero _ hh), ← hres, ← hres, ← evalRingHom_apply, ← evalRingHom_apply,
    ← evalRingHom_apply, ← map_pow, ← map_mul, ← map_pow, IsLocalization.mk'_spec]

variable [TopologicalSpace K]

/-- The value of `a ∈ Γ(X, U)` at points of `U(K)`, extended by `0` outside `U(K)`. -/
def evalExt (U : X.Opens) (a : Γ(X, U)) (p : UnderlyingSpace K X) : K :=
  open Classical in if h : ⊤ ≤ p.toHom ⁻¹ᵁ U then eval p h a else 0

/-- On points of `U(K)`, `evalExt U a` agrees with the value of `a`. -/
lemma evalExt_of_le {U : X.Opens} (a : Γ(X, U)) {p : UnderlyingSpace K X}
    (h : ⊤ ≤ p.toHom ⁻¹ᵁ U) : evalExt U a p = eval p h a :=
  dif_pos h

/-- `evalExt U a` is continuous on `U(K)`. -/
lemma continuousOn_evalExt (U : X.Opens) (a : Γ(X, U)) :
    ContinuousOn (evalExt (K := K) U a) {p | ⊤ ≤ p.toHom ⁻¹ᵁ U} := by
  rw [continuousOn_iff_continuous_restrict]
  exact (continuous_eval (K := K) U a).congr fun p ↦ (evalExt_of_le a p.2).symm

end Eval

section Pullback

variable {P A B S : Scheme.{u}} [P.Over (Spec (.of K))] [A.Over (Spec (.of K))]
  [B.Over (Spec (.of K))]

/-- The map `P(K) → A(K) × B(K)` induced by two morphisms out of `P`. -/
def prodMap (fst : P ⟶ A) (snd : P ⟶ B) [fst.IsOver (Spec (.of K))]
    [snd.IsOver (Spec (.of K))] (w : UnderlyingSpace K P) :
    UnderlyingSpace K A × UnderlyingSpace K B :=
  (mapFun fst w, mapFun snd w)

/-- For a pullback square, the map `P(K) → A(K) × B(K)` is injective. -/
lemma injective_prodMap_of_isPullback {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ S} {g : B ⟶ S}
    [fst.IsOver (Spec (.of K))] [snd.IsOver (Spec (.of K))] (H : IsPullback fst snd f g) :
    Function.Injective (prodMap (K := K) fst snd) := by
  intro w w' hw
  simp only [prodMap, Prod.mk.injEq] at hw
  exact UnderlyingSpace.ext (H.hom_ext (congrArg toHom hw.1) (congrArg toHom hw.2))

/-- A point of `P(K)` lies over the chart `pr₁⁻¹ U_A ∩ pr₂⁻¹ U_B` iff its two projections lie in
`U_A(K)` and `U_B(K)`. -/
lemma top_le_preimage_inf_iff (fst : P ⟶ A) (snd : P ⟶ B) [fst.IsOver (Spec (.of K))]
    [snd.IsOver (Spec (.of K))] (UA : A.Opens) (UB : B.Opens) (w : UnderlyingSpace K P) :
    ⊤ ≤ w.toHom ⁻¹ᵁ (fst ⁻¹ᵁ UA ⊓ snd ⁻¹ᵁ UB) ↔
      ⊤ ≤ (mapFun fst w).toHom ⁻¹ᵁ UA ∧ ⊤ ≤ (mapFun snd w).toHom ⁻¹ᵁ UB :=
  ⟨fun h ↦ ⟨fun _ hy ↦ (h hy).1, fun _ hy ↦ (h hy).2⟩,
    fun ⟨h1, h2⟩ _ hy ↦ ⟨h1 hy, h2 hy⟩⟩

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- The sections over `U_P` whose values are continuous functions of the two projections, on
the open set of pairs lying in `U_A(K) × U_B(K)`. -/
def continuousSections (fst : P ⟶ A) (snd : P ⟶ B) [fst.IsOver (Spec (.of K))]
    [snd.IsOver (Spec (.of K))] (UA : A.Opens) (UB : B.Opens) :
    Subring Γ(P, fst ⁻¹ᵁ UA ⊓ snd ⁻¹ᵁ UB) where
  carrier := {c | ∃ F : UnderlyingSpace K A × UnderlyingSpace K B → K,
    ContinuousOn F ({z | ⊤ ≤ z.1.toHom ⁻¹ᵁ UA} ∩ {z | ⊤ ≤ z.2.toHom ⁻¹ᵁ UB}) ∧
    ∀ (w : UnderlyingSpace K P) (hw : ⊤ ≤ w.toHom ⁻¹ᵁ (fst ⁻¹ᵁ UA ⊓ snd ⁻¹ᵁ UB)),
      eval w hw c = F (prodMap fst snd w)}
  mul_mem' := by
    rintro c d ⟨F, hF, hF'⟩ ⟨G, hG, hG'⟩
    refine ⟨F * G, hF.mul hG, fun w hw ↦ ?_⟩
    rw [← evalRingHom_apply, map_mul, evalRingHom_apply, evalRingHom_apply, hF', hG',
      Pi.mul_apply]
  one_mem' := ⟨1, continuousOn_const, fun w hw ↦ by
    rw [← evalRingHom_apply, map_one, Pi.one_apply]⟩
  add_mem' := by
    rintro c d ⟨F, hF, hF'⟩ ⟨G, hG, hG'⟩
    refine ⟨F + G, hF.add hG, fun w hw ↦ ?_⟩
    rw [← evalRingHom_apply, map_add, evalRingHom_apply, evalRingHom_apply, hF', hG',
      Pi.add_apply]
  zero_mem' := ⟨0, continuousOn_const, fun w hw ↦ by
    rw [← evalRingHom_apply, map_zero, Pi.zero_apply]⟩
  neg_mem' := by
    rintro c ⟨F, hF, hF'⟩
    refine ⟨-F, hF.neg, fun w hw ↦ ?_⟩
    rw [← evalRingHom_apply, map_neg, evalRingHom_apply, hF', Pi.neg_apply]

/-- The pull-back along `pr₁` of a section over `U_A` lies in `continuousSections`. -/
lemma appLE_fst_mem_continuousSections (fst : P ⟶ A) (snd : P ⟶ B)
    [fst.IsOver (Spec (.of K))] [snd.IsOver (Spec (.of K))] (UA : A.Opens) (UB : B.Opens)
    (a : Γ(A, UA)) :
    fst.appLE UA (fst ⁻¹ᵁ UA ⊓ snd ⁻¹ᵁ UB) inf_le_left a ∈
      continuousSections (K := K) fst snd UA UB := by
  refine ⟨fun z ↦ evalExt UA a z.1, ?_, fun w hw ↦ ?_⟩
  · exact (continuousOn_evalExt UA a).comp continuous_fst.continuousOn fun z hz ↦ hz.1
  · rw [eval_appLE]
    exact (evalExt_of_le _ _).symm

/-- The pull-back along `pr₂` of a section over `U_B` lies in `continuousSections`. -/
lemma appLE_snd_mem_continuousSections (fst : P ⟶ A) (snd : P ⟶ B)
    [fst.IsOver (Spec (.of K))] [snd.IsOver (Spec (.of K))] (UA : A.Opens) (UB : B.Opens)
    (b : Γ(B, UB)) :
    snd.appLE UB (fst ⁻¹ᵁ UA ⊓ snd ⁻¹ᵁ UB) inf_le_right b ∈
      continuousSections (K := K) fst snd UA UB := by
  refine ⟨fun z ↦ evalExt UB b z.2, ?_, fun w hw ↦ ?_⟩
  · exact (continuousOn_evalExt UB b).comp continuous_snd.continuousOn fun z hz ↦ hz.2
  · rw [eval_appLE]
    exact (evalExt_of_le _ _).symm

/-- On an affine chart `pr₁⁻¹ U_A ∩ pr₂⁻¹ U_B` of a pullback, every section has values that are
continuous functions of the two projections: the sections are generated by those pulled back
from `U_A` and `U_B`. -/
lemma mem_continuousSections {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ S} {g : B ⟶ S}
    [fst.IsOver (Spec (.of K))] [snd.IsOver (Spec (.of K))] (H : IsPullback fst snd f g)
    {US : S.Opens} {UA : A.Opens} {UB : B.Opens} (hUS : IsAffineOpen US)
    (hUA : IsAffineOpen UA) (hUB : IsAffineOpen UB) (hUAS : UA ≤ f ⁻¹ᵁ US)
    (hUBS : UB ≤ g ⁻¹ᵁ US) (c : Γ(P, fst ⁻¹ᵁ UA ⊓ snd ⁻¹ᵁ UB)) :
    c ∈ continuousSections (K := K) fst snd UA UB := by
  have hiso := isIso_pushoutSection_of_isAffineOpen H hUBS hUAS rfl hUS hUB hUA
  let T := continuousSections (K := K) fst snd UA UB
  let φA : Γ(A, UA) ⟶ CommRingCat.of T := CommRingCat.ofHom
    ((fst.appLE UA _ inf_le_left).hom.codRestrict T
      (appLE_fst_mem_continuousSections fst snd UA UB))
  let φB : Γ(B, UB) ⟶ CommRingCat.of T := CommRingCat.ofHom
    ((snd.appLE UB _ inf_le_right).hom.codRestrict T
      (appLE_snd_mem_continuousSections fst snd UA UB))
  have hcomm : f.appLE US UA hUAS ≫ φA = g.appLE US UB hUBS ≫ φB := by
    ext a
    change (f.appLE US UA hUAS ≫ fst.appLE UA _ inf_le_left) a =
      (g.appLE US UB hUBS ≫ snd.appLE UB _ inf_le_right) a
    simp only [Scheme.Hom.appLE_comp_appLE, H.w]
  have hk : Limits.pushout.desc φA φB hcomm ≫ CommRingCat.ofHom T.subtype =
      pushoutSection H hUBS hUAS rfl := by
    refine Limits.pushout.hom_ext ?_ ?_
    · rw [← Category.assoc, Limits.pushout.inl_desc, Limits.pushout.inl_desc]
      rfl
    · rw [← Category.assoc, Limits.pushout.inr_desc, Limits.pushout.inr_desc]
      rfl
  have : c = (Limits.pushout.desc φA φB hcomm ≫ CommRingCat.ofHom T.subtype)
      (inv (pushoutSection H hUBS hUAS rfl) c) := by
    rw [hk, ← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  rw [this]
  exact (Limits.pushout.desc φA φB hcomm (inv (pushoutSection H hUBS hUAS rfl) c)).2

variable [ContinuousInv₀ K] [T1Space K]

/-- The chart `pr₁⁻¹ U_A ∩ pr₂⁻¹ U_B` of a pullback of affine opens is affine. -/
lemma isAffineOpen_inf_of_isPullback {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ S} {g : B ⟶ S}
    (H : IsPullback fst snd f g) {US : S.Opens} {UA : A.Opens} {UB : B.Opens}
    (hUS : IsAffineOpen US) (hUA : IsAffineOpen UA) (hUB : IsAffineOpen UB)
    (hUAS : UA ≤ f ⁻¹ᵁ US) (hUBS : UB ≤ g ⁻¹ᵁ US) :
    IsAffineOpen (fst ⁻¹ᵁ UA ⊓ snd ⁻¹ᵁ UB) := by
  have : IsAffine US := hUS
  have : IsAffine UA := hUA
  have : IsAffine UB := hUB
  exact .of_isIso (Scheme.Hom.isPullback_resLE H hUBS hUAS rfl).isoPullback.hom

/-- For a pullback square, the map `P(K) → A(K) × B(K)` is inducing. -/
lemma isInducing_prodMap_of_isPullback {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ S} {g : B ⟶ S}
    [fst.IsOver (Spec (.of K))] [snd.IsOver (Spec (.of K))] (H : IsPullback fst snd f g) :
    IsInducing (prodMap (K := K) fst snd) := by
  rw [isInducing_iff]
  refine le_antisymm
    (continuous_iff_le_induced.mp ((map fst).continuous.prodMk (map snd).continuous))
    (le_generateFrom ?_)
  rintro _ ⟨V, s, W, hW, rfl⟩
  refine (@isOpen_iff_forall_mem_open _ (induced (prodMap fst snd) inferInstance) _).mpr ?_
  rintro w ⟨hw, hwW⟩
  obtain ⟨US, hUS, hxS, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := f (fst (w.toHom (IsLocalRing.closedPoint K)))) (U := ⊤) trivial
  obtain ⟨UA, hUA, hxA, hUAS⟩ := exists_isAffineOpen_mem_and_subset
    (x := fst (w.toHom (IsLocalRing.closedPoint K))) (U := f ⁻¹ᵁ US) hxS
  have hxS' : g (snd (w.toHom (IsLocalRing.closedPoint K))) ∈ US := by
    change (snd ≫ g) _ ∈ US
    rw [← H.w]
    exact hxS
  obtain ⟨UB, hUB, hxB, hUBS⟩ := exists_isAffineOpen_mem_and_subset
    (x := snd (w.toHom (IsLocalRing.closedPoint K))) (U := g ⁻¹ᵁ US) hxS'
  replace hUAS : UA ≤ f ⁻¹ᵁ US := hUAS
  replace hUBS : UB ≤ g ⁻¹ᵁ US := hUBS
  have hUY := isAffineOpen_inf_of_isPullback H hUS hUA hUB hUAS hUBS
  have hO : IsOpen ({z : UnderlyingSpace K A × UnderlyingSpace K B | ⊤ ≤ z.1.toHom ⁻¹ᵁ UA} ∩
      {z | ⊤ ≤ z.2.toHom ⁻¹ᵁ UB}) :=
    ((isOpen_setOf_le_preimage UA).preimage continuous_fst).inter
      ((isOpen_setOf_le_preimage UB).preimage continuous_snd)
  have hxUY : w.toHom (IsLocalRing.closedPoint K) ∈ fst ⁻¹ᵁ UA ⊓ snd ⁻¹ᵁ UB := ⟨hxA, hxB⟩
  have hxV : w.toHom (IsLocalRing.closedPoint K) ∈ V ⊓ (fst ⁻¹ᵁ UA ⊓ snd ⁻¹ᵁ UB) :=
    ⟨(top_le_preimage_iff w V).mp hw, hxUY⟩
  obtain ⟨h, hhV, hxh⟩ := hUY.exists_basicOpen_le ⟨_, hxV⟩ hxUY
  have := hUY.isLocalization_basicOpen h
  obtain ⟨⟨c, _, k, rfl⟩, hck⟩ := IsLocalization.mk'_surjective (Submonoid.powers h)
    (P.presheaf.map (homOfLE (hhV.trans inf_le_left)).op s)
  have hck' : IsLocalization.mk' (M := Submonoid.powers h) Γ(P, P.basicOpen h) c
      ⟨h ^ k, k, rfl⟩ = P.presheaf.map (homOfLE (hhV.trans inf_le_left)).op s := hck
  obtain ⟨Fh, hFh, hFh'⟩ := mem_continuousSections (K := K) H hUS hUA hUB hUAS hUBS h
  obtain ⟨Fc, hFc, hFc'⟩ := mem_continuousSections (K := K) H hUS hUA hUB hUAS hUBS c
  have hO' := hFh.isOpen_inter_preimage hO (isOpen_compl_singleton (x := (0 : K)))
  have hN := ContinuousOn.isOpen_inter_preimage (f := fun z ↦ Fc z / Fh z ^ k)
    ((hFc.mono Set.inter_subset_left).div ((hFh.mono Set.inter_subset_left).pow k)
      fun z hz ↦ pow_ne_zero _ hz.2) hO' hW
  have hval : ∀ w' : UnderlyingSpace K P, (hD : ⊤ ≤ w'.toHom ⁻¹ᵁ P.basicOpen h) →
      (hV : ⊤ ≤ w'.toHom ⁻¹ᵁ V) →
        eval w' hV s = Fc (prodMap fst snd w') / Fh (prodMap fst snd w') ^ k := by
    intro w' hD hV
    rw [← eval_restrict (hhV.trans inf_le_left) w' hD, ← hck', eval_mk'_of_isAffineOpen hUY,
      hFc', hFh']
  refine ⟨prodMap fst snd ⁻¹' _, ?_, isOpen_induced hN, ?_⟩
  · rintro w' ⟨⟨hO'w, hne⟩, hWw⟩
    have hw'Y := (top_le_preimage_inf_iff fst snd UA UB w').mpr hO'w
    have hD : ⊤ ≤ w'.toHom ⁻¹ᵁ P.basicOpen h := by
      rw [top_le_preimage_basicOpen_iff w' hw'Y, hFh']
      exact hne
    have hV := hD.trans (Scheme.Hom.preimage_mono _ (hhV.trans inf_le_left))
    exact ⟨hV, by rw [hval w' hD hV]; exact hWw⟩
  · have hD : ⊤ ≤ w.toHom ⁻¹ᵁ P.basicOpen h := (top_le_preimage_iff w _).mpr hxh
    have hwY : ⊤ ≤ w.toHom ⁻¹ᵁ (fst ⁻¹ᵁ UA ⊓ snd ⁻¹ᵁ UB) :=
      (top_le_preimage_iff w _).mpr hxUY
    refine ⟨⟨(top_le_preimage_inf_iff fst snd UA UB w).mp hwY, ?_⟩, ?_⟩
    · change Fh (prodMap fst snd w) ≠ 0
      rw [← hFh' w hwY, ← top_le_preimage_basicOpen_iff]
      exact hD
    · change Fc (prodMap fst snd w) / Fh (prodMap fst snd w) ^ k ∈ W
      rw [← hval w hD hw]
      exact hwW

/-- For a pullback square `P = A ×_S B` over `K`, the map `P(K) → A(K) × B(K)` is a topological
embedding. -/
theorem isEmbedding_prodMap_of_isPullback {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ S}
    {g : B ⟶ S} [fst.IsOver (Spec (.of K))] [snd.IsOver (Spec (.of K))]
    (H : IsPullback fst snd f g) :
    IsEmbedding (prodMap (K := K) fst snd) :=
  ⟨isInducing_prodMap_of_isPullback H, injective_prodMap_of_isPullback H⟩

end Pullback

section Range

variable {P A B S : Scheme.{u}} [P.Over (Spec (.of K))] [A.Over (Spec (.of K))]
  [B.Over (Spec (.of K))] [S.Over (Spec (.of K))]

/-- For a pullback square `P = A ×_S B` over `K`, the image of `P(K) → A(K) × B(K)` is the set
of pairs with the same image in `S(K)`. -/
theorem range_prodMap_of_isPullback {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ S} {g : B ⟶ S}
    [fst.IsOver (Spec (.of K))] [snd.IsOver (Spec (.of K))] [f.IsOver (Spec (.of K))]
    [g.IsOver (Spec (.of K))] (H : IsPullback fst snd f g) :
    Set.range (prodMap (K := K) fst snd) =
      {z | mapFun f z.1 = mapFun g z.2} := by
  ext ⟨a, b⟩
  refine ⟨?_, fun hab ↦ ?_⟩
  · rintro ⟨w, hw⟩
    simp only [prodMap, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact UnderlyingSpace.ext (by
      simp only [toHom_mapFun, Category.assoc, H.w])
  · have hab' : a.toHom ≫ f = b.toHom ≫ g := congrArg toHom hab
    refine ⟨⟨H.lift a.toHom b.toHom hab', ?_⟩, ?_⟩
    · rw [← comp_over fst (Spec (.of K)), ← Category.assoc, H.lift_fst, a.toHom_comp_over]
    · exact Prod.ext (UnderlyingSpace.ext (H.lift_fst _ _ _))
        (UnderlyingSpace.ext (H.lift_snd _ _ _))

end Range

end UnderlyingSpace

end MMP
