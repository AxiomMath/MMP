module

public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponentIntersection
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Unconditional

/-!
# Intersection numbers of a sheaf pulled back from the base

Let `u : X ⟶ Y` be a morphism of proper schemes over a field `k`, `M` an ample invertible sheaf
on `Y` and `A` an ample invertible sheaf on `X`. On a closed subscheme `Z ⊆ X` the intersection
numbers of `H = u^*M` and `A` are controlled by the dimension of the image `u(Z)`:

* if `u` maps `Z` to a point, `H|_Z` is trivial and every intersection number with a slot `H`
  vanishes;
* if `dim u(Z) < m`, an intersection number with `m` slots pulled back from `Y` and the others
  equal to `A` vanishes: the slots `A` are cut down by effective Cartier divisors of powers of
  `A`, and what remains is an intersection number of pull-backs against a subscheme whose image
  has too small a dimension ([Stacks, Tag 0BET]);
* if `Z` is integral of dimension `d + 1` and `u(Z)` is not a point, `(H · A^d · Z) > 0`: a power
  of `M` restricted to the integral image `u(Z)` is `𝒪(D)` for a nonempty effective Cartier
  divisor `D`, whose inverse image on `Z` cuts `H` down;
* every intersection number of `H` and `A` is nonnegative, `H` having nonnegative degrees on all
  integral closed subschemes.

For a curve-and-point exceptional model `r : Z ⟶ Y` with `H = r^*H_Y`, `H_Y` ample on `Y`, and
`A = N H - D` ample on every closed subscheme, these are the intersection numbers of `H` on the
components `Fᵢ` and on the double surfaces of `F`: `H ≡ 0` where the image is a point,
`(H|_E)^2 · A = 0` and `H|_E · A^2 > 0` on a threefold `E` over a curve, `(H|_S)^2 = 0` and
`H|_S · A|_S > 0` on a surface `S` over a curve, and `H|_S · A|_S ≥ 0` on every surface. Each is
stated with the component as a closed subscheme of a proper `k`-scheme `X` (for instance
`X = Fᵢ` and the identity), `u` the restriction of `r`.

## Main results

* `MMP.Fourfold.sheafIntersectionNumber_eq_zero_of_forall_eq`: a slot pulled back from a point.
* `MMP.Fourfold.sheafIntersectionNumber_eq_zero_of_isAmple_of_pullback`: too many slots pulled
  back from a small image.
* `MMP.Fourfold.sheafIntersectionNumber_pos_of_isAmple_of_pullback`: `(H · A^d · Z) > 0`.
* `MMP.Fourfold.sheafIntersectionNumber_nonneg_of_isAmple_of_pullback`: nonnegativity.
* `MMP.Fourfold.sheafIntersectionNumber_pullback_pullback_isAmple_eq_zero`,
  `MMP.Fourfold.sheafIntersectionNumber_pullback_isAmple_isAmple_pos`,
  `MMP.Fourfold.sheafIntersectionNumber_pullback_pullback_eq_zero`,
  `MMP.Fourfold.sheafIntersectionNumber_pullback_isAmple_pos`,
  `MMP.Fourfold.sheafIntersectionNumber_pullback_isAmple_nonneg`: the threefold and surface
  cases over a curve.

## Implementation notes

The work is done for the intersection numbers `AlgebraicGeometry.intersectionNumber` of the
Stacks project, where cutting down, the decomposition into top-dimensional components and
[Stacks, Tag 0BET] are available, and transported to `MMP.Mori.sheafIntersectionNumber` by
`MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber`. The image of `Z` enters through
the dimension of the set `u(Z)`; for a closed subscheme of a proper scheme it is the dimension of
the scheme-theoretic image.

## References

* [Stacks Project, Tag 0BET](https://stacks.math.columbia.edu/tag/0BET)
* [Stacks Project, Tag 0BES](https://stacks.math.columbia.edu/tag/0BES)
* [Stacks Project, Tag 0BEU](https://stacks.math.columbia.edu/tag/0BEU)
* [Stacks Project, Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV)
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Fourfold

open MMP.Mori

section Pullback

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k))
  (pY : Y ⟶ Spec (.of k)) [IsProper pX] [IsProper pY] (u : X ⟶ Y) (hu : u ≫ pY = pX)

/-- The scheme-theoretic image of a quasi-compact morphism with closed range has the dimension of
that range. -/
theorem topologicalKrullDim_image_eq_of_isClosed_range {Z : Scheme.{u}} (g : Z ⟶ Y)
    [QuasiCompact g] (hg : IsClosed (Set.range g.base)) :
    topologicalKrullDim g.image = topologicalKrullDim (Set.range g.base) := by
  rw [← Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_range_eq g.imageι,
    range_imageι_eq_closure_range g, hg.closure_eq]

include hu in
/-- **The pull-back of an ample invertible sheaf has nonnegative degrees.** Let `u : X ⟶ Y` be a
morphism of proper `k`-schemes and `M` an ample invertible sheaf on `Y`. For every integral
closed subscheme `W ⊆ X` of dimension `j`, `((u^*M)^j · W) ≥ 0`. -/
theorem intersectionNumber_pullback_nonneg_of_isAmple (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    (hM : Stacks.Ample.IsAmple Y M) {W : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i]
    [IsIntegral W] (j : ℕ) (hW : topologicalKrullDim W = (j : WithBot ℕ∞)) :
    0 ≤ intersectionNumber k pX i j hW.le (fun _ => (Scheme.Modules.pullback u).obj M) := by
  have hP : IsProper (i ≫ u) := isProper_comp_of_structureMap k pX pY u hu i
  have : UniversallyClosed (i ≫ u) := hP.toUniversallyClosed
  have : QuasiCompact (i ≫ u) := instQuasiCompactOfUniversallyClosed _
  have : LocallyOfFiniteType (i ≫ u) := hP.toLocallyOfFiniteType
  have hle : topologicalKrullDim (i ≫ u).image ≤ (j : WithBot ℕ∞) :=
    hW ▸ MMP.Mori.topologicalKrullDim_image_le pY (i ≫ u)
  rcases hle.lt_or_eq with hlt | heq
  · rw [intersectionNumber_pullback_eq_zero k pX pY u hu i j hW.le (fun _ => M) hlt]
  · rw [intersectionNumber_pullback_eq_degreeOver_mul k pX pY u hu i j hW (fun _ => M) heq]
    exact mul_nonneg (Int.natCast_nonneg _) (intersectionNumber_pos k pY _ j heq _
      fun _ => Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple Y M hM).le

include hu in
/-- If the support of a closed subscheme `W ⊆ X` lies in the range of `i : Z ⟶ X` and
`dim u(Z) < c`, then the scheme-theoretic image of `W` under `u` has dimension `< c`. -/
theorem topologicalKrullDim_image_lt_of_range_subset {Z W : Scheme.{u}} (i : Z ⟶ X)
    (j : W ⟶ X) [IsClosedImmersion j] (hji : Set.range j.base ⊆ Set.range i.base)
    {c : WithBot ℕ∞} (hc : topologicalKrullDim (Set.range (i ≫ u).base) < c) :
    topologicalKrullDim (j ≫ u).image < c := by
  have hP : IsProper (j ≫ u) := isProper_comp_of_structureMap k pX pY u hu j
  have : UniversallyClosed (j ≫ u) := hP.toUniversallyClosed
  have : QuasiCompact (j ≫ u) := instQuasiCompactOfUniversallyClosed _
  rw [topologicalKrullDim_image_eq_of_isClosed_range _ (j ≫ u).isClosedMap.isClosed_range]
  refine lt_of_le_of_lt
    (Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_le_of_subset ?_) hc
  rintro _ ⟨w, rfl⟩
  obtain ⟨z, hz⟩ := hji ⟨w, rfl⟩
  exact ⟨z, by simp [hz]⟩

/-- A top-dimensional integral component of a closed subscheme `Z ⊆ X` lies in `Z`. -/
theorem range_subschemeι_subset_of_topDimIntegralSubscheme {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (W : TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :
    Set.range W.1.subschemeι.base ⊆ Set.range i.base := by
  rw [Scheme.IdealSheafData.range_subschemeι, ← Stacks.Chow.supp_pushforwardStructureSheaf i]
  exact W.2.2.1

/-- A top-dimensional integral component of a closed subscheme `Z ⊆ X` has the dimension of `Z`. -/
theorem topologicalKrullDim_topDimIntegralSubscheme {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (W : TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :
    topologicalKrullDim W.1.subscheme = topologicalKrullDim Z := by
  rw [W.2.2.2, Stacks.Chow.supp_pushforwardStructureSheaf i,
    Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_range_eq i]

open Stacks.SheafOfModules.Invertible (tensorPower) in
/-- **Cutting down by a divisor of a tensor power.** If `D ⊆ Z` is an effective Cartier divisor
with `(F₀^{⊗n})|_Z ≅ 𝒪_Z(D)`, then `n · (F₀ ⋯ F_d · Z) = (F₁ ⋯ F_d · D)`. -/
theorem natCast_mul_intersectionNumber_eq_of_tensorPower_iso {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ ((d + 1 : ℕ) : WithBot ℕ∞))
    (F : Fin (d + 1) → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F q)] (n : ℕ)
    (D : Z.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hD : topologicalKrullDim D.subscheme ≤ (d : WithBot ℕ∞))
    (e : (Scheme.Modules.pullback i).obj (tensorPower X.presheaf X.ringCatSheaf.2 (F 0) (n : ℤ)) ≅
      Stacks.Divisors.invertibleSheaf D) :
    (n : ℤ) * intersectionNumber k pX i (d + 1) hd F =
      intersectionNumber k pX (D.subschemeι ≫ i) d hD fun t => F t.succ := by
  have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Function.update F 0 (tensorPower X.presheaf X.ringCatSheaf.2 (F 0) (n : ℤ)) q) :=
    isInvertible_update F 0 _
  rw [← intersectionNumber_update_tensorPower k pX i (d + 1) hd F 0 n,
    intersectionNumber_eq_of_isEffectiveCartierDivisor k pX i d hd _ D hD
      (eqToIso (congrArg (Scheme.Modules.pullback i).obj
        (Function.update_self (0 : Fin (d + 1)) _ F)) ≪≫ e)]
  exact intersectionNumber_congr_family k pX _ d _
    (funext fun t => Function.update_of_ne (Fin.succ_ne_zero t) _ _)

/-- **An ample sheaf against a family vanishing in codimension one.** Let `W ⊆ X` be an integral
closed subscheme of dimension `d + 1`, `A` ample on `X`, and `T₁, …, T_d` invertible sheaves with
`(T₁ ⋯ T_d · V) = 0` for every closed subscheme `V ⊆ W` of dimension `d`. Then
`(A · T₁ ⋯ T_d · W) = 0`. -/
theorem intersectionNumber_finCons_eq_zero_of_isAmple (A : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    (hA : Stacks.Ample.IsAmple X A) {W : Scheme.{u}} (j : W ⟶ X) [IsClosedImmersion j]
    [IsIntegral W] (d : ℕ) (hW : topologicalKrullDim W = ((d + 1 : ℕ) : WithBot ℕ∞))
    (T : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (T q)]
    (hT : ∀ {V : Scheme.{u}} (j' : V ⟶ X) [IsClosedImmersion j']
      (hV : topologicalKrullDim V = (d : WithBot ℕ∞)), Set.range j'.base ⊆ Set.range j.base →
        intersectionNumber k pX j' d hV.le T = 0) :
    haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        ((Fin.cons A T : Fin (d + 1) → X.Modules) q) := isInvertible_finCons A T
    intersectionNumber k pX j (d + 1) hW.le (Fin.cons A T) = 0 := by
  have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Fin.cons A T : Fin (d + 1) → X.Modules) q) := isInvertible_finCons A T
  have hposdim : 0 < topologicalKrullDim W := by
    rw [hW]
    exact_mod_cast Nat.succ_pos d
  have hAample : Scheme.Modules.IsAmple W ((Scheme.Modules.pullback j).obj A) :=
    Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
      (Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
        j A hA (Or.inl ⟨inferInstance, inferInstance⟩))
  obtain ⟨n, D, hn, hDc, hDne, ⟨e⟩⟩ :=
    exists_effectiveCartierDivisor_tensorPower_of_isAmple k (j ≫ pX) hposdim _ hAample
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hDc
  have hDdim : topologicalKrullDim D.subscheme = (d : WithBot ℕ∞) :=
    topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k (j ≫ pX) D hDc hW
  have hmul := natCast_mul_intersectionNumber_eq_of_tensorPower_iso k pX j d hW.le
    (Fin.cons A T) n D hDdim.le
    (Scheme.Modules.pullbackTensorPowerIso j ((Fin.cons A T : Fin (d + 1) → X.Modules) 0) n ≪≫ e)
  rw [intersectionNumber_congr_family k pX _ d _
      (funext fun t => Fin.cons_succ _ _ _ :
        (fun t : Fin d => (Fin.cons A T : Fin (d + 1) → X.Modules) t.succ) = T),
    hT (D.subschemeι ≫ j) hDdim
      (fun _ ⟨w, hw⟩ => ⟨D.subschemeι w, by simp [← hw]⟩)] at hmul
  exact (mul_eq_zero.1 hmul).resolve_left (by exact_mod_cast (show n ≠ 0 by omega))

include hu in
/-- For every closed subscheme `Z ⊆ X` of dimension `d` and every family of `d` invertible sheaves
equal to the ample sheaf `A` on a set `S` of `s` slots and to pull-backs `u^*Lⱼ` on the others,
`(F₁ ⋯ F_d · Z) = 0` whenever `dim u(Z) < d - s`. -/
theorem intersectionNumber_eq_zero_of_isAmple_of_pullback_of_card_eq (A : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    (hA : Stacks.Ample.IsAmple X A) (s : ℕ) :
    ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
      (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : Fin d → Y.Modules)
      [∀ q, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L q)]
      (F : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F q)]
      (S : Finset (Fin d)), S.card = s → (∀ q ∈ S, F q = A) →
      (∀ q ∉ S, F q = (Scheme.Modules.pullback u).obj (L q)) →
      topologicalKrullDim (Set.range (i ≫ u).base) < ((d - S.card : ℕ) : WithBot ℕ∞) →
      intersectionNumber k pX i d hd.le F = 0 := by
  classical
  induction s with
  | zero =>
    intro Z i _ d hdim L _ F _ S hs hSA hSL hlt
    rw [intersectionNumber_eq_sum_topDimComponents k pX i d hdim F]
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    have : IsIntegral W.1.subscheme := W.2.1
    rw [intersectionNumber_congr_family k pX W.1.subschemeι d _
      (funext fun q => hSL q (by simp [Finset.card_eq_zero.1 hs])),
      intersectionNumber_pullback_eq_zero k pX pY u hu W.1.subschemeι d _ L
        (topologicalKrullDim_image_lt_of_range_subset k pX pY u hu i _
          (range_subschemeι_subset_of_topDimIntegralSubscheme i W) (by simpa [hs] using hlt)),
      mul_zero]
  | succ s ih =>
    intro Z i _ d hdim L _ F _ S hs hSA hSL hlt
    have hSd : S.card ≤ d := (Finset.card_le_univ S).trans_eq (Fintype.card_fin d)
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨q0, hq0⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    let σ : Equiv.Perm (Fin (d' + 1)) := Equiv.swap 0 q0
    rw [← intersectionNumber_comp_perm k pX i (d' + 1) hdim.le F σ]
    set T : Fin d' → X.Modules := fun t => F (σ t.succ) with hT
    have hGeq : (fun q => F (σ q)) = (Fin.cons A T : Fin (d' + 1) → X.Modules) := by
      funext q
      refine Fin.cases ?_ (fun t => rfl) q
      simpa [σ] using hSA q0 hq0
    set S' : Finset (Fin d') := Finset.univ.filter fun t => σ t.succ ∈ S with hS'
    have hcard : S.card = S'.card + 1 := by
      have h := Equiv.sum_comp σ fun q => if q ∈ S then 1 else 0
      rw [Fin.sum_univ_succ] at h
      simp [σ, hq0] at h
      exact h.symm.trans (add_comm _ _)
    have hGinv : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        ((Fin.cons A T : Fin (d' + 1) → X.Modules) q) := isInvertible_finCons A T
    rw [intersectionNumber_congr_family k pX i (d' + 1) hdim.le hGeq,
      intersectionNumber_eq_sum_topDimComponents k pX i (d' + 1) hdim]
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    have : IsIntegral W.1.subscheme := W.2.1
    have hdimW : topologicalKrullDim W.1.subscheme = ((d' + 1 : ℕ) : WithBot ℕ∞) :=
      (topologicalKrullDim_topDimIntegralSubscheme i W).trans hdim
    refine mul_eq_zero_of_right _ (intersectionNumber_finCons_eq_zero_of_isAmple k pX A hA
      W.1.subschemeι d' hdimW T fun j' _ hV hj' => ?_)
    refine ih j' d' hV (fun t => L (σ t.succ)) T S' (by omega)
      (fun t ht => hSA _ (Finset.mem_filter.1 ht).2)
      (fun t ht => hSL _ fun h => ht (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)) ?_
    refine lt_of_le_of_lt
      (Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_le_of_subset ?_)
      (hlt.trans_eq (by rw [hcard, Nat.add_sub_add_right]))
    rintro _ ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := (hj'.trans (range_subschemeι_subset_of_topDimIntegralSubscheme i W)) ⟨w, rfl⟩
    exact ⟨z, by simp [hz]⟩

/-- The pull-back of an effective Cartier divisor along a dominant morphism of integral schemes is
nonzero. -/
theorem comap_ne_bot_of_isDominant {Z T : Scheme.{u}} [IsIntegral Z] [IsIntegral T] (f : Z ⟶ T)
    [IsDominant f] (D : T.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    D.comap f ≠ ⊥ := by
  intro hb
  refine genericPoint_notMem_supportSet_of_isEffectiveCartierDivisor hD ?_
  have hmem : genericPoint Z ∈ ((D.comap f).support : Set Z) := by
    rw [hb, Scheme.IdealSheafData.support_bot]
    trivial
  rw [Scheme.IdealSheafData.support_comap] at hmem
  rwa [← Stacks.Divisors.base_genericPoint_of_isDominant f]

/-- The pull-back along a surjective morphism of an ideal sheaf with nonempty subscheme has
nonempty subscheme. -/
theorem nonempty_subscheme_comap_of_surjective {Z T : Scheme.{u}} (f : Z ⟶ T)
    (hf : Surjective f) (D : T.IdealSheafData) (hD : Nonempty D.subscheme) :
    Nonempty (D.comap f).subscheme := by
  obtain ⟨t⟩ := hD
  obtain ⟨z, hz⟩ := hf.surj (D.subschemeι t)
  have hz' : z ∈ ((D.comap f).support : Set Z) := by
    rw [Scheme.IdealSheafData.support_comap]
    change f z ∈ (D.support : Set T)
    rw [hz, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨t, rfl⟩
  rw [← Scheme.IdealSheafData.range_subschemeι] at hz'
  obtain ⟨w, -⟩ := hz'
  exact ⟨w⟩

open Stacks.SheafOfModules.Invertible (tensorPower) in
include hu in
/-- **Positivity of `(u^*M · A^d · Z)` on a subvariety with positive-dimensional image.** Let
`u : X ⟶ Y` be a morphism of proper `k`-schemes, `M` an ample invertible sheaf on `Y`, `A` an
ample invertible sheaf on `X`, and `Z ⊆ X` an integral closed subscheme of dimension `d + 1`
whose image `u(Z)` has positive dimension. Then `(u^*M · A^d · Z) > 0`. -/
theorem intersectionNumber_pos_of_isAmple_of_pullback (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    (hM : Stacks.Ample.IsAmple Y M) (A : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    (hA : Stacks.Ample.IsAmple X A) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] (d : ℕ) (hZ : topologicalKrullDim Z = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hpos : 0 < topologicalKrullDim (Set.range (i ≫ u).base)) :
    haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        ((Fin.cons ((Scheme.Modules.pullback u).obj M) fun _ : Fin d => A :
          Fin (d + 1) → X.Modules) q) := isInvertible_finCons _ _
    0 < intersectionNumber k pX i (d + 1) hZ.le
      (Fin.cons ((Scheme.Modules.pullback u).obj M) fun _ : Fin d => A) := by
  classical
  set g := i ≫ u
  have hP : IsProper g := isProper_comp_of_structureMap k pX pY u hu i
  have : UniversallyClosed g := hP.toUniversallyClosed
  have : QuasiCompact g := instQuasiCompactOfUniversallyClosed _
  have : IsProper (g.imageι ≫ pY) := isProper_imageι_comp g pY
  have : UniversallyClosed g.toImage := (Stacks.Chow.isProper_toImage g).toUniversallyClosed
  have hsurj : Surjective g.toImage := Surjective.of_universallyClosed_of_isDominant g.toImage
  have : IsIntegral g.image := Stacks.Chow.isIntegral_image g
  have hTdim : 0 < topologicalKrullDim g.image := by
    rwa [topologicalKrullDim_image_eq_of_isClosed_range g g.isClosedMap.isClosed_range]
  have hMT : Scheme.Modules.IsAmple g.image ((Scheme.Modules.pullback g.imageι).obj M) :=
    Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
      (Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
        g.imageι M hM (Or.inl ⟨inferInstance, inferInstance⟩))
  obtain ⟨n, D, -, hDc, hDne, ⟨e⟩⟩ :=
    exists_effectiveCartierDivisor_tensorPower_of_isAmple k (g.imageι ≫ pY) hTdim _ hMT
  set G : Z.IdealSheafData := D.comap g.toImage
  have hGc : Stacks.Divisors.IsEffectiveCartierDivisor G :=
    Stacks.Divisors.isEffectiveCartierDivisor_of_isLocallyPrincipal G
      (comap_ne_bot_of_isDominant g.toImage D hDc)
      (Stacks.Divisors.isLocallyPrincipal_comap g.toImage D
        (Stacks.Divisors.isLocallyPrincipal_of_isEffectiveCartierDivisor D hDc))
  have : Nonempty G.subscheme := nonempty_subscheme_comap_of_surjective g.toImage hsurj D hDne
  have hGdim : topologicalKrullDim G.subscheme = (d : WithBot ℕ∞) :=
    topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k (i ≫ pX) G hGc hZ
  have hF : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Fin.cons ((Scheme.Modules.pullback u).obj M) fun _ : Fin d => A :
        Fin (d + 1) → X.Modules) q) := isInvertible_finCons _ _
  have : ∀ t : Fin d, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Fin.cons ((Scheme.Modules.pullback u).obj M) fun _ : Fin d => A :
        Fin (d + 1) → X.Modules) t.succ) := fun t => hF t.succ
  have hcut := natCast_mul_intersectionNumber_eq_of_tensorPower_iso k pX i d hZ.le
    (Fin.cons ((Scheme.Modules.pullback u).obj M) fun _ : Fin d => A) n G hGdim.le
    ((Scheme.Modules.pullback i).mapIso (Scheme.Modules.pullbackTensorPowerIso u M n).symm ≪≫
      (Scheme.Modules.pullbackComp i u).app _ ≪≫
      (Scheme.Modules.pullbackCongr g.toImage_imageι.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp g.toImage g.imageι).app _).symm ≪≫
      (Scheme.Modules.pullback g.toImage).mapIso
        (Scheme.Modules.pullbackTensorPowerIso g.imageι M n ≪≫ e) ≪≫
      Stacks.Divisors.invertibleSheafPullbackIso g.toImage D)
  refine pos_of_mul_pos_right (a := (n : ℤ)) ?_ (Int.natCast_nonneg n)
  rw [hcut, intersectionNumber_congr_family k pX _ d _
    (funext fun t => Fin.cons_succ _ _ _ : (fun t : Fin d =>
      (Fin.cons ((Scheme.Modules.pullback u).obj M) fun _ : Fin d => A :
        Fin (d + 1) → X.Modules) t.succ) = fun _ => A)]
  exact intersectionNumber_pos k pX (G.subschemeι ≫ i) d hGdim _
    fun _ => Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X A hA

/-! ### The intersection numbers of Kollár–Mori -/

/-- **A sheaf pulled back from a point kills the intersection number.** If `u : X ⟶ Y` maps
every point to `y` and one member of the family is `u^*M` for an invertible `M`, then
`(F₁ ⋯ F_d · Z) = 0`. -/
theorem sheafIntersectionNumber_eq_zero_of_forall_eq {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞))
    (F : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F q)]
    (y : Y) (hy : ∀ x, u x = y) (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] (j : Fin d)
    (hj : F j = (Scheme.Modules.pullback u).obj M) :
    sheafIntersectionNumber k pX i d hd F = 0 := by
  obtain ⟨e⟩ := nonempty_pullback_iso_unit_of_forall_eq u y hy M inferInstance
  exact sheafIntersectionNumber_eq_zero_of_iso_unit k pX i d hd F j (eqToIso hj ≪≫ e)

include hu in
/-- **Pull-backs of an ample sheaf against an ample sheaf are nonnegative.** Let `u : X ⟶ Y` be a
morphism of proper `k`-schemes, `M` ample on `Y` and `A` ample on `X`. Then
`(F₁ ⋯ F_d · Z) ≥ 0` for every closed subscheme `Z ⊆ X` of dimension at most `d` and every family
with each `Fⱼ` equal to `u^*M` or to `A`. -/
theorem sheafIntersectionNumber_nonneg_of_isAmple_of_pullback (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    (hM : Stacks.Ample.IsAmple Y M) (A : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    (hA : Stacks.Ample.IsAmple X A) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (F : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F q)]
    (hF : ∀ q, F q = (Scheme.Modules.pullback u).obj M ∨ F q = A) :
    0 ≤ sheafIntersectionNumber k pX i d hd F := by
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact MMP.Threefold.Mori.intersectionNumber_nonneg_of_isAmple_of_forall_eq_or_eq k pX _ A hA
    (fun j W i _ _ hW => intersectionNumber_pullback_nonneg_of_isAmple k pX pY u hu M hM i j hW)
    i d hd F hF

include hu in
/-- **Too many pull-backs from a small image kill the intersection number.** Let `u : X ⟶ Y`
be a morphism of proper `k`-schemes, `A` ample on `X`, `Z ⊆ X` a closed subscheme of dimension at
most `d`, and `F` a family of `d` invertible sheaves equal to `A` on a set `S` of slots and to
pull-backs `u^*Lⱼ` on the others. If `dim u(Z) < d - |S|`, then `(F₁ ⋯ F_d · Z) = 0`. -/
theorem sheafIntersectionNumber_eq_zero_of_isAmple_of_pullback (A : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    (hA : Stacks.Ample.IsAmple X A) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (L : Fin d → Y.Modules)
    [∀ q, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L q)]
    (F : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F q)]
    (S : Finset (Fin d)) (hSA : ∀ q ∈ S, F q = A)
    (hSL : ∀ q ∉ S, F q = (Scheme.Modules.pullback u).obj (L q))
    (hlt : topologicalKrullDim (Set.range (i ≫ u).base) < ((d - S.card : ℕ) : WithBot ℕ∞)) :
    sheafIntersectionNumber k pX i d hd F = 0 := by
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  rcases hd.lt_or_eq with h | h
  · exact intersectionNumber_eq_zero_of_topologicalKrullDim_lt k pX i d hd h F
  · exact intersectionNumber_eq_zero_of_isAmple_of_pullback_of_card_eq k pX pY u hu A hA _ i d h
      L F S rfl hSA hSL hlt

include hu in
/-- **Positivity of `(u^*M · A^d · Z)`**, for the intersection numbers of Kollár–Mori: see
`MMP.Fourfold.intersectionNumber_pos_of_isAmple_of_pullback`. -/
theorem sheafIntersectionNumber_pos_of_isAmple_of_pullback (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    (hM : Stacks.Ample.IsAmple Y M) (A : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    (hA : Stacks.Ample.IsAmple X A) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] (d : ℕ) (hZ : topologicalKrullDim Z = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hpos : 0 < topologicalKrullDim (Set.range (i ≫ u).base)) (F : Fin (d + 1) → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F q)]
    (hF0 : F 0 = (Scheme.Modules.pullback u).obj M) (hFA : ∀ t : Fin d, F t.succ = A) :
    0 < sheafIntersectionNumber k pX i (d + 1) hZ.le F := by
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  have hFeq : F = Fin.cons ((Scheme.Modules.pullback u).obj M) fun _ : Fin d => A := by
    funext q
    refine Fin.cases ?_ (fun t => ?_) q
    · exact hF0
    · exact hFA t
  have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Fin.cons ((Scheme.Modules.pullback u).obj M) fun _ : Fin d => A :
        Fin (d + 1) → X.Modules) q) := isInvertible_finCons _ _
  rw [intersectionNumber_congr_family k pX i (d + 1) hZ.le hFeq]
  exact intersectionNumber_pos_of_isAmple_of_pullback k pX pY u hu M hM A hA i d hZ hpos

/-! ### Threefolds and surfaces over a curve -/

section CurveImage

variable (M : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
  (A : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
  {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

include hu in
/-- **`((u^*M)^2 · A · Z) = 0` when `dim u(Z) ≤ 1`**, for `Z` of dimension at most three and `A`
ample: the self-intersection of a sheaf pulled back from a curve vanishes. -/
theorem sheafIntersectionNumber_pullback_pullback_isAmple_eq_zero
    (hA : Stacks.Ample.IsAmple X A) (hd : topologicalKrullDim Z ≤ (3 : ℕ))
    (him : topologicalKrullDim (Set.range (i ≫ u).base) ≤ 1) :
    haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (![(Scheme.Modules.pullback u).obj M, (Scheme.Modules.pullback u).obj M, A] t) :=
      fun t => by fin_cases t <;> dsimp <;> infer_instance
    sheafIntersectionNumber k pX i 3 hd
      ![(Scheme.Modules.pullback u).obj M, (Scheme.Modules.pullback u).obj M, A] = 0 := by
  have : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![(Scheme.Modules.pullback u).obj M, (Scheme.Modules.pullback u).obj M, A] t) :=
    fun t => by fin_cases t <;> dsimp <;> infer_instance
  refine sheafIntersectionNumber_eq_zero_of_isAmple_of_pullback k pX pY u hu A hA i 3 hd
    (fun _ => M) _ {2} (fun q hq => ?_) (fun q hq => ?_) (him.trans_lt ?_)
  · obtain rfl := Finset.mem_singleton.1 hq
    rfl
  · fin_cases q
    · rfl
    · rfl
    · exact absurd (Finset.mem_singleton_self _) hq
  · simp only [Finset.card_singleton]
    exact_mod_cast (show (1 : ℕ) < 3 - 1 by norm_num)

include hu in
/-- **`(u^*M · A^2 · Z) > 0` when `u(Z)` is not a point**, for `Z` an integral threefold, `M`
ample on `Y` and `A` ample on `X`. -/
theorem sheafIntersectionNumber_pullback_isAmple_isAmple_pos (hM : Stacks.Ample.IsAmple Y M)
    (hA : Stacks.Ample.IsAmple X A) [IsIntegral Z]
    (hZ : topologicalKrullDim Z = ((2 + 1 : ℕ) : WithBot ℕ∞))
    (hpos : 0 < topologicalKrullDim (Set.range (i ≫ u).base)) :
    haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (![(Scheme.Modules.pullback u).obj M, A, A] t) :=
      fun t => by fin_cases t <;> dsimp <;> infer_instance
    0 < sheafIntersectionNumber k pX i 3 hZ.le ![(Scheme.Modules.pullback u).obj M, A, A] := by
  have : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![(Scheme.Modules.pullback u).obj M, A, A] t) :=
    fun t => by fin_cases t <;> dsimp <;> infer_instance
  exact sheafIntersectionNumber_pos_of_isAmple_of_pullback k pX pY u hu M hM A hA i 2 hZ hpos _ rfl
    fun t => by fin_cases t <;> rfl

include hu in
/-- **`((u^*M)^2 · S) = 0` when `dim u(S) ≤ 1`**, for `S` of dimension at most two. -/
theorem sheafIntersectionNumber_pullback_pullback_eq_zero (hA : Stacks.Ample.IsAmple X A)
    (hd : topologicalKrullDim Z ≤ (2 : ℕ))
    (him : topologicalKrullDim (Set.range (i ≫ u).base) ≤ 1) :
    haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (![(Scheme.Modules.pullback u).obj M, (Scheme.Modules.pullback u).obj M] t) :=
      fun t => by fin_cases t <;> dsimp <;> infer_instance
    sheafIntersectionNumber k pX i 2 hd
      ![(Scheme.Modules.pullback u).obj M, (Scheme.Modules.pullback u).obj M] = 0 := by
  have : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![(Scheme.Modules.pullback u).obj M, (Scheme.Modules.pullback u).obj M] t) :=
    fun t => by fin_cases t <;> dsimp <;> infer_instance
  refine sheafIntersectionNumber_eq_zero_of_isAmple_of_pullback k pX pY u hu A hA i 2 hd
    (fun _ => M) _ ∅ (fun q hq => absurd hq (Finset.notMem_empty q)) (fun q _ => ?_)
    (him.trans_lt ?_)
  · fin_cases q <;> rfl
  · simp only [Finset.card_empty]
    exact_mod_cast (show (1 : ℕ) < 2 - 0 by norm_num)

include hu in
/-- **`(u^*M · A · S) > 0` when `u(S)` is not a point**, for `S` an integral surface, `M` ample
on `Y` and `A` ample on `X`. -/
theorem sheafIntersectionNumber_pullback_isAmple_pos (hM : Stacks.Ample.IsAmple Y M)
    (hA : Stacks.Ample.IsAmple X A) [IsIntegral Z]
    (hZ : topologicalKrullDim Z = ((1 + 1 : ℕ) : WithBot ℕ∞))
    (hpos : 0 < topologicalKrullDim (Set.range (i ≫ u).base)) :
    haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (![(Scheme.Modules.pullback u).obj M, A] t) :=
      fun t => by fin_cases t <;> dsimp <;> infer_instance
    0 < sheafIntersectionNumber k pX i 2 hZ.le ![(Scheme.Modules.pullback u).obj M, A] := by
  have : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![(Scheme.Modules.pullback u).obj M, A] t) :=
    fun t => by fin_cases t <;> dsimp <;> infer_instance
  exact sheafIntersectionNumber_pos_of_isAmple_of_pullback k pX pY u hu M hM A hA i 1 hZ hpos _ rfl
    fun t => by
      fin_cases t
      rfl

include hu in
/-- **`(u^*M · A · S) ≥ 0`** for every closed subscheme `S` of dimension at most two, `M` ample
on `Y` and `A` ample on `X`: a nef sheaf against an ample one. -/
theorem sheafIntersectionNumber_pullback_isAmple_nonneg (hM : Stacks.Ample.IsAmple Y M)
    (hA : Stacks.Ample.IsAmple X A) (hd : topologicalKrullDim Z ≤ (2 : ℕ)) :
    haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (![(Scheme.Modules.pullback u).obj M, A] t) :=
      fun t => by fin_cases t <;> dsimp <;> infer_instance
    0 ≤ sheafIntersectionNumber k pX i 2 hd ![(Scheme.Modules.pullback u).obj M, A] := by
  have : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![(Scheme.Modules.pullback u).obj M, A] t) :=
    fun t => by fin_cases t <;> dsimp <;> infer_instance
  exact sheafIntersectionNumber_nonneg_of_isAmple_of_pullback k pX pY u hu M hM A hA i 2 hd _
    fun q => by fin_cases q <;> simp

end CurveImage

end Pullback

end MMP.Fourfold
