module
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Sequence
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Functor
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative
public import MMP.AlgebraicGeometry.Resolution.BlowupChartCoordinates
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.MaximalContact.LogDerivations
import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientPowers
import MMP.AlgebraicGeometry.Resolution.Surface.SncPointsCompletions

/-!
# Orders, cosupports and blow-up sequences of order `m`

On a scheme whose local rings are regular (for instance a smooth scheme over a field) the order
of an ideal is multiplicative under powers, `ord_x (I ^ c) = c · ord_x I`. This file collects
the consequences of that fact, and of the local structure of a smooth blow-up, used in Kollár's
proof of resolution of singularities.

* Raising a marked ideal `(I, m)` to `(I ^ c, m c)` does not change its cosupport.
* If the centre `Z` of a blow-up `π : B_Z X → X` is an effective Cartier divisor whose
  components have codimension one, then `π` is an isomorphism and the total transform of a
  reduced ordered divisor `E = (E^1, …, E^s)` is `(E^1, …, E^s, Z^♮)`, where `Z^♮` is the
  reduced union of the components of `Z` that are not components of `Supp E`.
* On a blow-up chart `U_ℓ` with coordinates `y`, if `π^*f = y_ℓ^m g`, then for every index
  `j > r` (off the centre coordinates) `π^*(∂f/∂x_j) = y_ℓ^m ∂g/∂y_j`.
* The pull-back of a smooth blow-up sequence of order `m` along an étale morphism `ψ` is a
  smooth blow-up sequence of order `≥ m`, whose marked ideals are the pull-backs of the
  controlled transforms.
* The centres of a smooth blow-up sequence of order `m` lie over `cosupp(I, m)`, and along a
  sequence of order `≥ m` the cosupport of the `i`-th birational transform lies over
  `cosupp(I, m)`.
* For a marked triple, the mixed ideal `K_s(I, m) = N(I)^m + I^s` has maximal order at most
  `m·s`, and `ord_x J₁ ≥ s ∧ ord_x J₂ ≥ m ↔ ord_x (J₁ ^ m + J₂ ^ s) ≥ m·s`.

## Main results

* `MMP.Resolution.MarkedIdeal.cosupport_pow`
* `MMP.Resolution.OrderedDivisor.totalTransform_eq_comap_of_isEffectiveCartierDivisor`
* `MMP.Resolution.BlowupChartData.appLE_partialDerivative_eq_pow_mul_of_le`
* `MMP.Resolution.ClosedBlowupSequence.isOrderGePlainSeq_pullback_of_etale`
* `MMP.Resolution.ClosedBlowupSequence.centersLieOver_cosupport_of_isOrderMPlainSeq`
* `MMP.Resolution.ClosedBlowupSequence.cosupport_markedTransform_truncate_subset`
* `MMP.Resolution.maxOrder_mixedIdeal_le`
* `MMP.Resolution.le_multAt_pow_sup_pow_iff`

## Implementation notes

The identification `B_Z X = X` for a Cartier centre is made by pulling back along
`blowUpToBase Z`. Partial derivatives are read on affine opens
(`MMP.Resolution.partialDerivative`): the chart identity is stated on every affine open
`W ⊆ U_ℓ ∩ π⁻¹(W')` for every affine open `W' ⊆ U`; these cover `U_ℓ`. The function `g` is any
section with `π^*f = (π^*x_ℓ)^m g`. The `i`-th stage of a pulled-back sequence is read on the
truncation `B.truncate i`.

That a smooth centre `Z` with `ord_Z I ≥ m` lies in `cosupp(I, m)` is read off the pointwise
bound `I_x ⊆ (I_Z)_x ^ m` (`MMP.Resolution.stalk_le_pow_of_orderAlongGE`), rather than through
the generic points of the components of `Z` and the closedness of the cosupport. Off the
centre the blow-up is a local isomorphism under which the transforms are the pull-back of `I`.

The sum of ideal sheaves is the supremum `⊔` in `X.IdealSheafData`; orders are
`MMP.Resolution.multAt`, valued in `ℕ∞`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.59, 3.65, (3.75.2), 3.66, 3.97,
  3.111]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

universe u

namespace MMP.Resolution

/-! ### Cosupport of a power -/

/-- On a scheme with regular local rings, `cosupp(I, m) = cosupp(I ^ c, m c)` for every
`c ≠ 0`. -/
@[mmp "lem_kr3c_marked_cosupport_power"]
public theorem MarkedIdeal.cosupport_pow {X : Scheme.{u}}
    [∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)]
    (I : X.IdealSheafData) (m : ℕ) {c : ℕ} (hc : c ≠ 0) :
    (⟨I, m⟩ : MarkedIdeal X).cosupport = (⟨I ^ c, m * c⟩ : MarkedIdeal X).cosupport := by
  ext x
  simp only [MarkedIdeal.cosupport, Set.mem_setOf_eq, multAt_pow, Nat.cast_mul]
  rw [mul_comm (m : ℕ∞)]
  exact (ENat.mul_le_mul_left_iff (by exact_mod_cast hc) (ENat.coe_ne_top c)).symm

/-! ### The total transform under a trivial blow-up -/

/-- Along an isomorphism, the pushforward of an ideal sheaf is its pullback along the inverse. -/
private lemma map_eq_comap_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (I : X.IdealSheafData) :
    I.map f = I.comap (inv f) := by
  apply le_antisymm
  · have h := Scheme.IdealSheafData.comap_mono (inv f)
      (Scheme.IdealSheafData.comap_map_le (f := f) (I := I))
    simpa [← Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_id] using h
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp]
    simp [Scheme.IdealSheafData.comap_id]

/-- Pulling back the reduced structure on a closure along an isomorphism. -/
private lemma comap_vanishingIdeal_closure {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f]
    (S : Set X) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure S)).comap f =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (f.base ⁻¹' S)) := by
  have h : ∀ J : X.IdealSheafData, J.comap f = J.map (inv f) := fun J => by
    rw [map_eq_comap_inv, IsIso.inv_inv]
  rw [h, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  apply SetLike.coe_injective
  simp only [Closeds.coe_closure]
  have himg : ∀ T : Set X, (inv f).base '' T = f.base ⁻¹' T := fun T =>
    congrFun (Set.image_eq_preimage_of_inverse (f := (inv f).base) (g := f.base)
      (fun x => by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl)
      (fun y => by rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl)) T
  rw [himg, f.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage f.continuous,
    closure_closure]

/-- If `Z` is an effective Cartier divisor all of whose irreducible components have codimension
one and every `E^i` is reduced, the total transform of `E` along `π : B_ZX → X` (an
isomorphism) is the pullback along `π` of `(E^1, …, E^s, Z^♮)`, with `Z^♮` the reduced union of
the irreducible components of `Z` that are not irreducible components of `E.support`. -/
@[mmp "lem_kr3c_total_transform_trivial_blowup"]
public theorem OrderedDivisor.totalTransform_eq_comap_of_isEffectiveCartierDivisor
    {X : Scheme.{u}} (E : OrderedDivisor X) (Z : X.IdealSheafData)
    (hE : ∀ i, IsReduced (E.E i).subscheme)
    (hZ : Stacks.Divisors.IsEffectiveCartierDivisor Z)
    (hcodim : ∀ (W : Set X) (hW : W ∈ componentsOf (Z.support : Set X)),
      codimension (irreducibleClosure hW.1.1) = 1) :
    E.totalTransform Z =
      (⟨E.s + 1, Fin.snoc (α := fun _ => X.IdealSheafData) E.E
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
          (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
            (_ : W ∉ componentsOf E.support), W)))⟩ : OrderedDivisor X).comap
        (blowUpToBase Z) := by
  haveI := Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor Z hZ
  have h2 : componentsOfCodimAtLeastTwo (Z.support : Set X) = ∅ := by
    ext x
    simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
    rintro ⟨W, hW, h, -⟩
    rw [hcodim W hW] at h
    exact absurd h (by decide)
  simp only [OrderedDivisor.totalTransform, OrderedDivisor.comap, h2, Set.diff_empty]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Fin.snoc_last]
    rw [comap_vanishingIdeal_closure, Set.preimage_iUnion₂]
    simp only [Set.preimage_iUnion]
  · simp only [Fin.snoc_castSucc]
    haveI := hE i
    conv_rhs => rw [← MMP.Mori.vanishingIdeal_support_eq_self (E.E i)]
    have hc : Closeds.closure ((E.E i).support : Set X) = (E.E i).support :=
      SetLike.coe_injective (E.E i).support.isClosed.closure_eq
    rw [← hc, comap_vanishingIdeal_closure, hc]

/-! ### Partial derivatives on a blow-up chart -/

namespace BlowupChartData

open MMP.Flips.ResolutionInputs

private theorem restrictSection_mul {Y : Scheme.{u}} {V : Y.Opens} (W : Y.affineOpens)
    (h : W.1 ≤ V) (a b : Γ(Y, V)) :
    restrictSection W h (a * b) = restrictSection W h a * restrictSection W h b :=
  map_mul _ a b

private theorem restrictSection_pow {Y : Scheme.{u}} {V : Y.Opens} (W : Y.affineOpens)
    (h : W.1 ≤ V) (a : Γ(Y, V)) (m : ℕ) :
    restrictSection W h (a ^ m) = restrictSection W h a ^ m :=
  map_pow _ a m

/-- Restricting a chart pullback to an affine open of the chart is the `appLE` to that open. -/
private theorem restrictSection_chartPullback {X : Scheme.{u}} {Z : X.IdealSheafData}
    (c : BlowupChartData Z) (ℓ : Fin c.r) (W : (blowUp Z).affineOpens) (hW : W.1 ≤ c.chart ℓ)
    (s : Γ(X, c.U)) :
    restrictSection W hW (c.chartPullback ℓ s) =
      ((blowUpToBase Z).appLE c.U W (hW.trans (c.chart_le ℓ))).hom s := by
  unfold restrictSection chartPullback
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- Pulling back a restriction along `appLE` is restricting the chart pullback. -/
private theorem appLE_restrictSection {X : Scheme.{u}} {Z : X.IdealSheafData}
    (c : BlowupChartData Z) (ℓ : Fin c.r) (W' : X.affineOpens) (hW' : W'.1 ≤ c.U)
    (W : (blowUp Z).affineOpens) (hW : W.1 ≤ c.chart ℓ) (hWW' : W.1 ≤ blowUpToBase Z ⁻¹ᵁ W'.1)
    (s : Γ(X, c.U)) :
    ((blowUpToBase Z).appLE W' W hWW').hom (restrictSection W' hW' s) =
      restrictSection W hW (c.chartPullback ℓ s) := by
  rw [restrictSection_chartPullback c ℓ W hW]
  unfold restrictSection
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

section ChartDerivative

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {Z : X.IdealSheafData} (c : BlowupChartData Z) {n : ℕ} {x : Fin n → Γ(X, c.U)}
  (hrn : c.r ≤ n) (hcx : ∀ i, c.x i = x (Fin.castLE hrn i)) (ℓ : Fin c.r)
  (hy : IsLocalCoordinatesOn (blowUpToBase Z ≫ sX) (c.chart ℓ) (chartCoordinates c x ℓ))
  (W : (blowUp Z).affineOpens) (hW : W.1 ≤ c.chart ℓ) {j : Fin n}

include hcx in
/-- On the chart `U_ℓ`, the pullback of `x_ℓ` is a chart coordinate other than `y_j` for
`j ≥ r`, so its partial derivative in `y_j` vanishes. -/
private theorem partialDerivative_chartPullback_x_self (hj : c.r ≤ (j : ℕ)) :
    partialDerivative hy W hW j (restrictSection W hW (c.chartPullback ℓ (c.x ℓ))) = 0 := by
  have hℓ : chartCoordinates c x ℓ (Fin.castLE hrn ℓ) = c.chartPullback ℓ (c.x ℓ) := by
    rw [hcx]
    exact chartCoordinates_of_forall_ne c x hrn fun i hi h =>
      hi (Fin.ext (by simpa using congrArg Fin.val h))
  rw [← hℓ, Bridges.partialDerivative_restrictSection_coordinate, if_neg]
  exact fun h => by have := congrArg Fin.val h; simp at this; omega

include hcx in
/-- For `j ≥ r`, the pulled-back base coordinates satisfy `∂(π^*x_i)/∂y_j = δ_ij` on the
chart `U_ℓ`: for `i < r` the pullback is `y_i · π^*x_ℓ` (or `π^*x_ℓ` itself), and for
`i ≥ r` it is the chart coordinate `y_i`. -/
private theorem partialDerivative_chartPullback_coordinate (hj : c.r ≤ (j : ℕ)) (i : Fin n) :
    partialDerivative hy W hW j (restrictSection W hW (c.chartPullback ℓ (x i))) =
      if i = j then 1 else 0 := by
  let := MMP.Mori.sectionAlgebra (blowUpToBase Z ≫ sX) W.1
  have hdℓ := partialDerivative_chartPullback_x_self c hrn hcx ℓ hy W hW hj
  by_cases hi : (i : ℕ) < c.r
  · have hij : i ≠ j := fun h => by subst h; omega
    set i' : Fin c.r := ⟨i, hi⟩
    rw [if_neg hij, show x i = c.x i' by rw [hcx]; rfl]
    by_cases hiℓ : i' = ℓ
    · rw [hiℓ, hdℓ]
    · rw [chartPullback_eq_chartFraction_mul, restrictSection_mul,
        ← Bridges.partialDerivation_apply, Derivation.leibniz, Bridges.partialDerivation_apply,
        Bridges.partialDerivation_apply, hdℓ,
        ← chartCoordinates_castLE_of_ne c x hrn hiℓ,
        Bridges.partialDerivative_restrictSection_coordinate, if_neg]
      · simp
      · exact fun h => hij (h ▸ rfl)
  · rw [← show chartCoordinates c x ℓ i = c.chartPullback ℓ (x i) by
        rw [chartCoordinates, dif_neg hi],
      Bridges.partialDerivative_restrictSection_coordinate]
    exact if_congr eq_comm rfl rfl

end ChartDerivative

/-- **Kollár (3.75.2).** Let `x_1, …, x_n` be local coordinates on `U` whose first `r` are the
generators `c.x` of the centre, `y = chartCoordinates c x ℓ` the coordinates on the chart
`U_ℓ`, and `f ∈ 𝒪_X(U)`, `g ∈ 𝒪(U_ℓ)` with `π^*f = (π^*x_ℓ)^m g`. Then for `j > r`,
`π^*(∂f/∂x_j) = (π^*x_ℓ)^m · ∂g/∂y_j` on every affine open `W ⊆ U_ℓ ∩ π⁻¹(W')`, `W' ⊆ U`
affine. -/
@[mmp "lem_kr3d_chart_derivative_index_above"]
public theorem appLE_partialDerivative_eq_pow_mul_of_le {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {Z : X.IdealSheafData} (c : BlowupChartData Z)
    {n : ℕ} {x : Fin n → Γ(X, c.U)} (hx : IsLocalCoordinatesOn sX c.U x) (hrn : c.r ≤ n)
    (hcx : ∀ i, c.x i = x (Fin.castLE hrn i)) (ℓ : Fin c.r)
    (hy : IsLocalCoordinatesOn (blowUpToBase Z ≫ sX) (c.chart ℓ) (chartCoordinates c x ℓ))
    (f : Γ(X, c.U)) (m : ℕ) (g : Γ(blowUp Z, c.chart ℓ))
    (hfg : c.chartPullback ℓ f = c.chartPullback ℓ (c.x ℓ) ^ m * g)
    (W' : X.affineOpens) (hW' : W'.1 ≤ c.U) (W : (blowUp Z).affineOpens)
    (hW : W.1 ≤ c.chart ℓ) (hWW' : W.1 ≤ blowUpToBase Z ⁻¹ᵁ W'.1)
    (j : Fin n) (hj : c.r ≤ (j : ℕ)) :
    ((blowUpToBase Z).appLE W' W hWW').hom
        (partialDerivative hx W' hW' j (restrictSection W' hW' f)) =
      restrictSection W hW (c.chartPullback ℓ (c.x ℓ)) ^ m *
        partialDerivative hy W hW j (restrictSection W hW g) := by
  let := MMP.Mori.sectionAlgebra (blowUpToBase Z ≫ sX) W.1
  have chain := Kollar.partialDerivative_appLE_eq_sum (blowUpToBase Z) rfl hx hy W' hW' W hW hWW'
    (restrictSection W' hW' f) j
  simp_rw [← restrictSection_chartPullback c ℓ W hW,
    partialDerivative_chartPullback_coordinate c hrn hcx ℓ hy W hW hj, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at chain
  rw [← chain, appLE_restrictSection c ℓ W' hW' W hW, hfg, restrictSection_mul, restrictSection_pow,
    ← Bridges.partialDerivation_apply, Derivation.leibniz, Derivation.leibniz_pow,
    Bridges.partialDerivation_apply, Bridges.partialDerivation_apply,
    partialDerivative_chartPullback_x_self c hrn hcx ℓ hy W hW hj]
  simp [smul_eq_mul]

end BlowupChartData

/-! ### Étale pull-back of a blow-up sequence of order `m` -/

/-- The inverse image of a smooth centre along an étale morphism is smooth. -/
private theorem isSmoothScheme_comap_subschemeι {k : Type u} [Field k] {X U : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (ψ : U ⟶ X) [Etale ψ] (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) :
    MMP.Mori.IsSmoothScheme ((Z.comap ψ).subschemeι ≫ ψ ≫ sX) := by
  haveI := hZ.smooth
  have he : (Z.comap ψ).subschemeι ≫ ψ ≫ sX =
      (Z.comapIso ψ).hom ≫ Limits.pullback.snd ψ Z.subschemeι ≫ Z.subschemeι ≫ sX := by
    rw [← Z.comapIso_hom_fst ψ, Category.assoc, Limits.pullback.condition_assoc]
  rw [he]
  exact MMP.Mori.isSmoothScheme_of_smooth inferInstance

/-- Along a flat morphism, the components of the inverse image of a closed subset whose
components have positive codimension again have positive codimension. -/
private theorem hasComponentsOfPositiveCodim_preimage {X U : Scheme.{u}} (ψ : U ⟶ X) [Flat ψ]
    {Z : Set X} (hZc : IsClosed Z) (hZ : HasComponentsOfPositiveCodim Z) :
    HasComponentsOfPositiveCodim (ψ ⁻¹' Z) := by
  intro W hW
  by_contra hlt
  have h0 : codimension (irreducibleClosure hW.1.1) = 0 := by
    rw [not_le] at hlt
    exact ENat.lt_one_iff_eq_zero.1 hlt
  rw [codimension_eq_coheight, Order.coheight_eq_zero] at h0
  have hWc : IsClosed W := isClosed_of_mem_componentsOf (hZc.preimage ψ.continuous) hW
  have hη := hW.1.1.isGenericPoint_genericPoint_closure
  set η := hW.1.1.genericPoint
  have hηW : η ∈ W := hWc.closure_subset hη.mem
  set W' : Set X := closure {ψ η}
  have hW'irr : IsIrreducible W' := isIrreducible_singleton.closure
  -- `W'` is maximal among irreducible closed subsets of `X`.
  have hmax : ∀ T : Set X, IsIrreducible T → W' ⊆ T → closure T ⊆ W' := by
    intro T hT hTW
    have hξ := hT.isGenericPoint_genericPoint_closure
    have hsp : hT.genericPoint ⤳ ψ η :=
      hξ.specializes (subset_closure (hTW (subset_closure rfl)))
    obtain ⟨η', hη'η, hψη'⟩ := Flat.generalizingMap ψ hsp
    have hle : irreducibleClosure hW.1.1 ≤
        ⟨closure {η'}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
      change closure W ⊆ closure {η'}
      rw [hWc.closure_eq]
      intro w hw
      exact (hη'η.trans (hη.specializes (subset_closure hw))).mem_closure
    have hη'mem : η' ∈ closure W := h0 hle (subset_closure rfl)
    have : η' = η := ((hη.specializes hη'mem).antisymm hη'η).eq.symm
    rw [← hξ.def, ← hψη', this]
  have hW'Z : W' ⊆ Z := hZc.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hW.1.2 hηW))
  have hW'comp : W' ∈ componentsOf Z :=
    ⟨⟨hW'irr, hW'Z⟩, fun V hV hWV => subset_closure.trans (hmax V hV.1 hWV)⟩
  have h1 := hZ W' hW'comp
  have : Order.coheight (irreducibleClosure hW'comp.1.1) = 0 := by
    rw [Order.coheight_eq_zero]
    intro T hT
    change closure W' ⊆ (T : Set X) at hT
    change (T : Set X) ⊆ closure W'
    rw [closure_closure] at hT ⊢
    have := hmax T T.isIrreducible hT
    rwa [T.isClosed.closure_eq] at this
  rw [← codimension_eq_coheight] at this
  rw [this] at h1
  exact absurd h1 (by norm_num)

/-- Order bound along the inverse image of a smooth centre: if `ord_Z I ≥ m` along a smooth
centre `Z` of a smooth `X`, then `ord ψ^*I ≥ m` along `ψ⁻¹Z` for any morphism `ψ`. -/
private theorem orderAlongGE_comap {k : Type u} [Field k] {X U : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) (ψ : U ⟶ X)
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (m : ℕ) (hI : OrderAlongGE I (Z.support : Set X) m) :
    OrderAlongGE (I.comap ψ) ((Z.comap ψ).support : Set U) m := by
  intro W hW
  have hWc : IsClosed W := isClosed_of_mem_componentsOf (Z.comap ψ).support.2 hW
  have hηW : hW.1.1.genericPoint ∈ W :=
    hWc.closure_subset hW.1.1.isGenericPoint_genericPoint_closure.mem
  set η := hW.1.1.genericPoint
  have hηZ : ψ η ∈ (Z.support : Set X) := by
    have := hW.1.2 hηW
    rwa [Scheme.IdealSheafData.support_comap] at this
  change (m : ℕ∞) ≤ idealOrder (IdealSheafData.stalk (I.comap ψ) η)
  rw [natCast_le_idealOrder_iff', IdealSheafData.stalk_comap]
  have h1 := stalk_le_pow_of_orderAlongGE sX hX Z hZ I m hI (ψ η)
  have h2 : IdealSheafData.stalk Z (ψ η) ≤ maximalIdeal _ :=
    IsLocalRing.le_maximalIdeal fun h =>
      ((IdealSheafData.stalk_eq_top_iff_notMem_support Z _).1 h) hηZ
  refine (Ideal.map_mono (h1.trans (Ideal.pow_right_mono h2 m))).trans ?_
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) m

/-- Along a smooth centre of constant order `m`, the divisor of the controlled transform is
`I_F^m`. -/
private theorem controlledTransformDivisorIdeal_eq_pow {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (m : ℕ) (hI : OrderAlongEq I (Z.support : Set X) m) :
    controlledTransformDivisorIdeal Z I = Z.comap (blowUpToBase Z) ^ m := by
  classical
  haveI := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := ⟨⟩
  haveI : Finite (componentsOf (Z.support : Set X)) :=
    (finite_componentsOf Z.support.2).to_subtype
  letI := Fintype.ofFinite (componentsOf (Z.support : Set X))
  refine IdealSheafData.eq_of_stalk_eq _ _ fun y => ?_
  set x := blowUpToBase Z y
  have hD : IdealSheafData.stalk (controlledTransformDivisorIdeal Z I) y =
      ∏ W : componentsOf (Z.support : Set X), Ideal.map ((blowUpToBase Z).stalkMap y).hom
        (IdealSheafData.stalk (componentsFamily (Z.support : Set X) W) x) ^
          (orderAlong I W.2.1.1).toNat := by
    unfold controlledTransformDivisorIdeal
    rw [finprod_eq_prod_of_fintype, stalk_prod]
    refine Finset.prod_congr rfl fun W _ => ?_
    rw [IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
  rw [hD, IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
  by_cases hx : x ∈ (Z.support : Set X)
  · obtain ⟨W0, hW0, hxW0, huniq, hstalk, -⟩ := exists_component_through sX hX Z hZ I x hx
    rw [Finset.prod_eq_single (⟨W0, hW0⟩ : componentsOf (Z.support : Set X))]
    · rw [hstalk, hI W0 hW0]
      rfl
    · intro W _ hne
      have : x ∉ (W : Set X) := fun hxW => hne (Subtype.ext (huniq W W.2 hxW))
      simp [Ideal.map_top, stalk_componentsFamily_eq_top Z W.2 this]
    · simp
  · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support Z x).2 hx]
    refine (Finset.prod_eq_one fun W _ => ?_).trans (by simp [Ideal.map_top, Ideal.top_pow])
    simp [Ideal.map_top, stalk_componentsFamily_eq_top Z W.2 fun hxW => hx (W.2.1.2 hxW)]

/-- Cancellation of an effective Cartier divisor: `J·D = J'·D` implies `J = J'`. -/
private theorem eq_of_mul_eq_mul_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    {D : X.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    {J J' : X.IdealSheafData} (h : J * D = J' * D) : J = J' := by
  have key : ∀ {A B : X.IdealSheafData}, A * D = B * D → A ≤ B := by
    intro A B hAB
    refine IdealSheafData.le_of_stalk_le _ _ fun y a ha => ?_
    obtain ⟨g, hg, hgs⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor D hD y
    have hs := congrArg (fun K => IdealSheafData.stalk K y) hAB
    simp only [IdealSheafData.stalk_mul, hgs] at hs
    have hga : g * a ∈ Ideal.span {g} * IdealSheafData.stalk B y := by
      rw [← mul_comm (IdealSheafData.stalk B y), ← hs, mul_comm]
      exact Ideal.mem_span_singleton_mul.2 ⟨a, ha, rfl⟩
    obtain ⟨z, hz, hzg⟩ := Ideal.mem_span_singleton_mul.1 hga
    rwa [← hg.1 hzg]
  exact le_antisymm (key h) (key h.symm)

/-- **One step.** The birational transform of `(ψ^*I, m)` along `ψ⁻¹Z` is the inverse image of
the controlled transform of `I` along the canonical lift. -/
private theorem birationalTransform_comap_eq {k : Type u} [Field k] {X U : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (ψ : U ⟶ X) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (I : X.IdealSheafData)
    (hI : IsNonzeroAtGenericPoints I) (m : ℕ) (hord : OrderAlongEq I (Z.support : Set X) m)
    (hU : MMP.Mori.IsSmoothScheme (ψ ≫ sX))
    (hZU : MMP.Mori.IsSmoothScheme ((Z.comap ψ).subschemeι ≫ ψ ≫ sX))
    (hcodimU : HasComponentsOfPositiveCodim ((Z.comap ψ).support : Set U))
    (hordU : OrderAlongGE (I.comap ψ) ((Z.comap ψ).support : Set U) m) :
    (MarkedIdeal.birationalTransform (Z.comap ψ) ⟨I.comap ψ, m⟩) =
      ⟨(controlledTransform Z I).comap (canonicalLift ψ Z), m⟩ := by
  have hc := canonicalLift_comp_blowUpToBase ψ Z
  have hDc : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Z.comap ψ).comap (blowUpToBase (Z.comap ψ)) ^ m) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (Z.comap ψ)) m
  have h1 := MarkedIdeal.birationalTransform_mul_eq (ψ ≫ sX) hU (Z.comap ψ) hZU hcodimU
    ⟨I.comap ψ, m⟩ hordU
  have h2 := controlledTransform_mul_eq sX hX Z hZ hcodim I hI
  rw [controlledTransformDivisorIdeal_eq_pow sX hX Z hZ I m hord] at h2
  have hF : (Z.comap ψ).comap (blowUpToBase (Z.comap ψ)) =
      (Z.comap (blowUpToBase Z)).comap (canonicalLift ψ Z) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hc]
  have h3 : (controlledTransform Z I).comap (canonicalLift ψ Z) *
      (Z.comap ψ).comap (blowUpToBase (Z.comap ψ)) ^ m =
      (I.comap ψ).comap (blowUpToBase (Z.comap ψ)) := by
    rw [hF, ← Stacks.IdealSheaf.comap_pow, ← Stacks.IdealSheaf.comap_mul, h2,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hc]
  have := eq_of_mul_eq_mul_of_isEffectiveCartierDivisor hDc (h1.trans h3.symm)
  change MarkedIdeal.mk _ m = MarkedIdeal.mk _ m
  rw [← this]
  rfl

/-- The canonical lift of an étale morphism is étale. -/
private theorem etale_canonicalLift {X U : Scheme.{u}} (ψ : U ⟶ X) [Etale ψ]
    (Z : X.IdealSheafData) : Etale (canonicalLift ψ Z) :=
  MorphismProperty.of_isPullback (P := @Etale) (Kollar.isPullback_canonicalLift_of_flat ψ Z) ‹_›

/-- The induction along the sequence behind `isOrderGePlainSeq_pullback_of_etale`, with the
structure morphism and the étale morphism generalised. -/
private theorem isOrderGePlainSeq_pullback_of_etale_aux {k : Type u} [Field k] {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) :
    ∀ (sX : X ⟶ Spec (.of k)) (_ : LocallyOfFiniteType sX) (_ : QuasiCompact sX)
      (I : X.IdealSheafData) (m : ℕ) (_ : B.IsOrderMPlainSeq sX I m)
      {U : Scheme.{u}} (ψ : U ⟶ X) (_ : Etale ψ),
    (B.pullback ψ).IsOrderGePlainSeq (ψ ≫ sX) ⟨I.comap ψ, m⟩ ∧
      ∀ i : ℕ, ((B.truncate i).pullback ψ).markedTransform ⟨I.comap ψ, m⟩ =
        ⟨((B.truncate i).controlledTransform I).comap ((B.truncate i).pullbackHom ψ), m⟩ := by
  induction B with
  | nil X =>
    intro sX _ _ I m hB U ψ _
    obtain ⟨hX, hI⟩ := hB
    haveI := hX.smooth
    exact ⟨⟨MMP.Mori.isSmoothScheme_of_smooth inferInstance,
      isNonzeroAtGenericPoints_comap_of_flat ψ hI⟩, fun _ => rfl⟩
  | cons Z B ih =>
    intro sX _ _ I m hB U ψ _
    obtain ⟨hX, hI, hZ, hcodim, hord, hB'⟩ := hB
    haveI := hX.smooth
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsProper (blowUpToBase Z) := isProper_blowUpToBase Z
    have hU : MMP.Mori.IsSmoothScheme (ψ ≫ sX) := MMP.Mori.isSmoothScheme_of_smooth inferInstance
    have hZU := isSmoothScheme_comap_subschemeι sX ψ Z hZ
    have hcodimU : HasComponentsOfPositiveCodim ((Z.comap ψ).support : Set U) := by
      rw [Scheme.IdealSheafData.support_comap]
      exact hasComponentsOfPositiveCodim_preimage ψ Z.support.2 hcodim
    have hordU := orderAlongGE_comap sX hX ψ Z hZ I m (fun W hW => (hord W hW).ge)
    have hbt := birationalTransform_comap_eq sX hX ψ Z hZ hcodim I hI m hord hU hZU hcodimU hordU
    obtain ⟨ih1, ih2⟩ := ih (blowUpToBase Z ≫ sX) inferInstance inferInstance
      (controlledTransform Z I) m hB' (canonicalLift ψ Z) (etale_canonicalLift ψ Z)
    have hc : canonicalLift ψ Z ≫ blowUpToBase Z ≫ sX = blowUpToBase (Z.comap ψ) ≫ ψ ≫ sX := by
      rw [← Category.assoc, canonicalLift_comp_blowUpToBase, Category.assoc]
    refine ⟨⟨hU, isNonzeroAtGenericPoints_comap_of_flat ψ hI, hZU, hcodimU, hordU, ?_⟩, ?_⟩
    · change (B.pullback (canonicalLift ψ Z)).IsOrderGePlainSeq
        (blowUpToBase (Z.comap ψ) ≫ ψ ≫ sX)
        (MarkedIdeal.birationalTransform (Z.comap ψ) ⟨I.comap ψ, m⟩)
      rw [hbt, ← hc]
      exact ih1
    · intro i
      cases i with
      | zero => rfl
      | succ i =>
        change ((B.truncate i).pullback (canonicalLift ψ Z)).markedTransform
            (MarkedIdeal.birationalTransform (Z.comap ψ) ⟨I.comap ψ, m⟩) = _
        rw [hbt]
        exact ih2 i

namespace ClosedBlowupSequence

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **Étale pull-back of an order-`m` sequence.** Let `X` be smooth, equidimensional, of finite
type over a field `k` of characteristic `0`;
`I` an ideal sheaf nonzero on every irreducible component with `maxOrder I ≤ m`, `1 ≤ m`; and
`B` a smooth blow-up sequence of order `m` starting with `(X, I)`. For étale `ψ : U ⟶ X`,
`B.pullback ψ` is a smooth blow-up sequence of order `≥ m` starting with `(U, ψ^*I, m)`, and for
every `i` its `i`-th marked ideal is `(ψ_i^*I_i, m)`, with `ψ_i = (B.truncate i).pullbackHom ψ`
and `I_i = (B.truncate i).controlledTransform I`. -/
@[mmp "lem_kr3d_etale_pullback_sequence_order"]
public theorem isOrderGePlainSeq_pullback_of_etale {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX] (hXeq : TopologicalSpace.Equidimensional X)
    (I : X.IdealSheafData) (hI : IsNonzeroAtGenericPoints I) (m : ℕ) (hm : 1 ≤ m)
    (hmax : maxOrder I ≤ m) (B : ClosedBlowupSequence X) (hB : B.IsOrderMPlainSeq sX I m)
    {U : Scheme.{u}} (ψ : U ⟶ X) [Etale ψ] :
    (B.pullback ψ).IsOrderGePlainSeq (ψ ≫ sX) ⟨I.comap ψ, m⟩ ∧
      ∀ i : ℕ, ((B.truncate i).pullback ψ).markedTransform ⟨I.comap ψ, m⟩ =
        ⟨((B.truncate i).controlledTransform I).comap ((B.truncate i).pullbackHom ψ), m⟩ :=
  isOrderGePlainSeq_pullback_of_etale_aux B sX inferInstance inferInstance I m hB ψ inferInstance

end ClosedBlowupSequence

/-! ### Centres and cosupports along a sequence of order `m` -/

/-- The order of an ideal does not drop under an isomorphism of local rings: if
`m ≤ ord (φ J)` then `m ≤ ord J`. -/
private theorem natCast_le_idealOrder_of_map {R S : CommRingCat.{u}} [IsLocalRing R]
    [IsLocalRing S] (φ : R ⟶ S) [IsIso φ] {J : Ideal R} {m : ℕ}
    (h : (m : ℕ∞) ≤ idealOrder (J.map φ.hom)) : (m : ℕ∞) ≤ idealOrder J := by
  rw [natCast_le_idealOrder_iff'] at h ⊢
  have hJ : J = (J.map φ.hom).map (inv φ).hom := by
    rw [Ideal.map_map, ← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]
  rw [hJ]
  refine (Ideal.map_mono h).trans ?_
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono
    (Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap _).ge) m

/-- A smooth centre `Z` along which `ord_Z I ≥ m` lies in `cosupp(I, m)`. -/
private theorem support_subset_cosupport {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme s) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) (I : X.IdealSheafData) (m : ℕ)
    (ha : OrderAlongGE I (Z.support : Set X) m) :
    (Z.support : Set X) ⊆ MarkedIdeal.cosupport ⟨I, m⟩ := by
  intro x hx
  change (m : ℕ∞) ≤ idealOrder (IdealSheafData.stalk I x)
  refine (natCast_le_idealOrder_iff' _ _).2 <|
    (stalk_le_pow_of_orderAlongGE s hX Z hZ I m ha _).trans (Ideal.pow_right_mono ?_ _)
  exact le_maximalIdeal ((IdealSheafData.stalk_eq_top_iff_notMem_support _ _).not.2
    (not_not.2 hx))

/-- **One blow-up.** For a smooth centre `Z` of a smooth `X` along which `ord_Z I ≥ m`, the
cosupport of `(π⁻¹_{Z*}I, m)` lies over `cosupp(I, m)`. -/
private theorem cosupport_controlledTransform_subset {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme s) [LocallyOfFiniteType s]
    [QuasiCompact s] (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (I : X.IdealSheafData)
    (hI : IsNonzeroAtGenericPoints I) (m : ℕ) (ha : OrderAlongGE I (Z.support : Set X) m) :
    MarkedIdeal.cosupport ⟨controlledTransform Z I, m⟩ ⊆
      blowUpToBase Z ⁻¹' MarkedIdeal.cosupport ⟨I, m⟩ := by
  intro y (hy : (m : ℕ∞) ≤ idealOrder (IdealSheafData.stalk (controlledTransform Z I) y))
  by_cases hx : blowUpToBase Z y ∈ (Z.support : Set X)
  · exact support_subset_cosupport s hX Z hZ I m ha hx
  · change (m : ℕ∞) ≤ idealOrder (IdealSheafData.stalk I (blowUpToBase Z y))
    have := isIso_stalkMap_of_isIso_morphismRestrict _
      (isIso_blowUpToBase_restrict_compl_support Z) (show y ∈ _ ⁻¹ᵁ Z.support.compl from hx)
    have htop : IdealSheafData.stalk (controlledTransformDivisorIdeal Z I) y = ⊤ := by
      obtain ⟨n, hn, -⟩ := exists_stalk_divisor_eq s hX Z hZ I y
      rw [hn, (IdealSheafData.stalk_eq_top_iff_notMem_support _ y).2
        (by rwa [Scheme.IdealSheafData.support_comap]), Ideal.top_pow]
    have hm := congrArg (IdealSheafData.stalk · y)
      (controlledTransform_mul_eq s hX Z hZ hcodim I hI)
    simp only [IdealSheafData.stalk_mul, htop, IdealSheafData.stalk_comap, Ideal.mul_top] at hm
    exact natCast_le_idealOrder_of_map _ (hm ▸ hy)

/-- **One blow-up.** For a smooth centre `Z` of a smooth `X` along which `ord_Z I ≥ m`, the
cosupport of the birational transform lies over the cosupport of `(I, m)`. -/
private theorem cosupport_birationalTransform_subset {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme s) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (a : MarkedIdeal X)
    (ha : OrderAlongGE a.I (Z.support : Set X) a.m) :
    (a.birationalTransform Z).cosupport ⊆ blowUpToBase Z ⁻¹' a.cosupport := by
  intro y (hy : (a.m : ℕ∞) ≤ idealOrder (IdealSheafData.stalk (a.birationalTransform Z).I y))
  by_cases hx : blowUpToBase Z y ∈ (Z.support : Set X)
  · exact support_subset_cosupport s hX Z hZ a.I a.m ha hx
  · change (a.m : ℕ∞) ≤ idealOrder (IdealSheafData.stalk a.I (blowUpToBase Z y))
    have := isIso_stalkMap_of_isIso_morphismRestrict _
      (isIso_blowUpToBase_restrict_compl_support Z) (show y ∈ _ ⁻¹ᵁ Z.support.compl from hx)
    have htop : IdealSheafData.stalk (Z.comap (blowUpToBase Z)) y = ⊤ := by
      rwa [IdealSheafData.stalk_eq_top_iff_notMem_support, Scheme.IdealSheafData.support_comap]
    have hm := congrArg (IdealSheafData.stalk · y)
      (MarkedIdeal.birationalTransform_mul_eq s hX Z hZ hcodim a ha)
    simp only [IdealSheafData.stalk_mul, IdealSheafData.stalk_pow, htop,
      IdealSheafData.stalk_comap, Ideal.top_pow, Ideal.mul_top] at hm
    exact natCast_le_idealOrder_of_map _ (hm ▸ hy)

namespace ClosedBlowupSequence

/-- The induction behind `centersLieOver_cosupport_of_isOrderMPlainSeq`: with `f : X ⟶ X₀` and
`cosupp(I, m) ⊆ f⁻¹ S`, the centres lie over `S`. -/
private theorem centersLieOver_of_cosupport_subset {k : Type u} [Field k] {X X₀ : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s] (I : X.IdealSheafData)
    (m : ℕ) (B : ClosedBlowupSequence X) (hB : B.IsOrderMPlainSeq s I m) (f : X ⟶ X₀)
    (S : Set X₀) (hS : MarkedIdeal.cosupport ⟨I, m⟩ ⊆ f ⁻¹' S) : B.CentersLieOver f S := by
  induction B generalizing X₀ with
  | nil X => trivial
  | cons Z B ih =>
    obtain ⟨hX, hI, hZ, hcodim, hord, hB'⟩ := hB
    have ha : OrderAlongGE I (Z.support : Set _) m := fun W hW => (hord W hW).ge
    haveI : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian s
    refine ⟨?_, ih _ _ hB' _ S ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hS (support_subset_cosupport s hX Z hZ I m ha hx)
    · exact fun y hy => hS (cosupport_controlledTransform_subset s hX Z hZ hcodim I hI m ha hy)

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **Centres of an order-`m` sequence lie over the cosupport.** Let `X` be smooth,
equidimensional, of finite type over a field `k` of characteristic `0`; `I` an ideal sheaf nonzero
on every irreducible component with `maxOrder I ≤ m`, `1 ≤ m`; and `B` a smooth blow-up sequence of
order `m` starting with `(X, I)`. Then the image in `X` of every centre of `B` lies in the
cosupport of the marked ideal `(I, m)`. -/
@[mmp "lem_kr3d_order_m_sequence_over_cosupport"]
public theorem centersLieOver_cosupport_of_isOrderMPlainSeq {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX] (hXeq : TopologicalSpace.Equidimensional X)
    (I : X.IdealSheafData) (hI : IsNonzeroAtGenericPoints I) (m : ℕ) (hm : 1 ≤ m)
    (hmax : maxOrder I ≤ m) (B : ClosedBlowupSequence X) (hB : B.IsOrderMPlainSeq sX I m) :
    B.CentersLieOver (𝟙 X) (MarkedIdeal.cosupport ⟨I, m⟩) :=
  centersLieOver_of_cosupport_subset sX I m B hB (𝟙 X) _ subset_rfl

/-- Along a smooth blow-up sequence of order `≥ m` starting with a marked triple `(X, I, m, E)`,
the cosupport of the `i`-th birational transform lies over the cosupport of `(I, m)`:
`cosupp(I_i, m) ⊆ Π_i⁻¹(cosupp(I, m))`. -/
@[mmp "lem_kr3e_cosupport_disjointness_preserved"]
public theorem cosupport_markedTransform_truncate_subset {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X)
    (B : ClosedBlowupSequence X) (hB : B.IsOrderGeMarkedTripleSeq s a E) (i : ℕ) :
    ((B.truncate i).markedTransform a).cosupport ⊆ (B.truncate i).toBase ⁻¹' a.cosupport := by
  induction B generalizing i with
  | nil X => exact subset_rfl
  | cons Z B ih =>
    cases i with
    | zero => exact subset_rfl
    | succ i =>
      obtain ⟨hT, hZ, hcodim, -, ha, hB'⟩ := hB
      exact fun y hy =>
        cosupport_birationalTransform_subset s hT.2.1 Z hZ hcodim a ha (ih _ _ _ hB' i hy)

end ClosedBlowupSequence

/-! ### Orders of sums of powers and the mixed ideal -/

/-- For a marked triple `(X, I, m, E)` with `m ≥ 1` and `s = maxord_{cosupp(I, m)} N(I) ≥ 1`,
the ideal `K_s(I, m) = N(I)^m + I^s` has maximal order at most `m·s`. -/
@[mmp "lem_kr3e_mixed_ideal_max_order"]
public theorem maxOrder_mixedIdeal_le {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X) (m s : ℕ)
    (hT : IsTriple sX I E) (hm : 1 ≤ m)
    (hs : maxOrderAlong (nonmonomialPart I E) (MarkedIdeal.cosupport ⟨I, m⟩) = s)
    (hs1 : 1 ≤ s) :
    maxOrder (mixedIdeal I E m s) ≤ ((m * s : ℕ) : ℕ∞) := by
  obtain ⟨-, hsm, hlft, -⟩ := hT
  haveI : LocallyOfFiniteType sX := hlft
  haveI : Smooth sX := Aux.smooth_of_isSmoothScheme' sX hsm
  refine iSup₂_le fun x _ => ?_
  haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth_over_field sX x
  -- an ideal containing `J ^ n` has order at most `n · ord_x J`
  have hpow : ∀ {J K : X.IdealSheafData} {n : ℕ}, J ^ n ≤ K → multAt K x ≤ n * multAt J x :=
    fun h => (Kollar.multAt_antitone h x).trans_eq (multAt_pow x _ _)
  push_cast
  by_cases hx : (m : ℕ∞) ≤ multAt I x
  · have hN : multAt (nonmonomialPart I E) x ≤ s :=
      hs ▸ le_iSup₂ (f := fun z (_ : z ∈ MarkedIdeal.cosupport ⟨I, m⟩) =>
        multAt (nonmonomialPart I E) z) x hx
    calc _ ≤ m * multAt (nonmonomialPart I E) x := hpow le_sup_left
      _ ≤ m * s := by gcongr
  · calc _ ≤ s * multAt I x := hpow le_sup_right
      _ ≤ s * m := by gcongr; exact (not_le.mp hx).le
      _ = m * s := mul_comm _ _

/-- The stalk of a sum of ideal sheaves is the sum of the stalks. -/
private theorem stalk_sup {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I ⊔ J) x = IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hx,
    IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hx,
    IdealSheafData.stalk_eq_map_germ J x ⟨U, hU⟩ hx,
    show (I ⊔ J).ideal ⟨U, hU⟩ = I.ideal ⟨U, hU⟩ ⊔ J.ideal ⟨U, hU⟩ from rfl, Ideal.map_sup]

/-- `n ≤ ord_x (I ⊔ J)` iff `n ≤ ord_x I` and `n ≤ ord_x J`. -/
private theorem natCast_le_multAt_sup_iff {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X)
    (n : ℕ) : (n : ℕ∞) ≤ multAt (I ⊔ J) x ↔ (n : ℕ∞) ≤ multAt I x ∧ (n : ℕ∞) ≤ multAt J x := by
  simp only [multAt, natCast_le_idealOrder_iff', stalk_sup, sup_le_iff]

/-- Cancelling a positive natural factor in `a * b ≤ a * y` over `ℕ∞`. -/
private theorem natCast_mul_le_iff {a b : ℕ} (ha : 1 ≤ a) (y : ℕ∞) :
    ((a * b : ℕ) : ℕ∞) ≤ a * y ↔ (b : ℕ∞) ≤ y := by
  push_cast
  exact ENat.mul_le_mul_left_iff (by exact_mod_cast (by omega : a ≠ 0)) (ENat.coe_ne_top a)

/-- On a smooth scheme of finite type over a field, `ord_x J₁ ≥ s` and `ord_x J₂ ≥ m` if and only
if `ord_x (J₁ ^ m + J₂ ^ s) ≥ m · s`, for `s, m ≥ 1`. -/
@[mmp "lem_kr3e_order_of_sum_of_powers"]
public theorem le_multAt_pow_sup_pow_iff {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hXeq : TopologicalSpace.Equidimensional X)
    (J₁ J₂ : X.IdealSheafData) {s m : ℕ} (hs : 1 ≤ s) (hm : 1 ≤ m) (x : X) :
    ((s : ℕ∞) ≤ multAt J₁ x ∧ (m : ℕ∞) ≤ multAt J₂ x) ↔
      ((m * s : ℕ) : ℕ∞) ≤ multAt (J₁ ^ m ⊔ J₂ ^ s) x := by
  haveI : Smooth sX := Aux.smooth_of_isSmoothScheme' sX hX
  haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth_over_field sX x
  rw [natCast_le_multAt_sup_iff, multAt_pow, multAt_pow, natCast_mul_le_iff hm, mul_comm m s,
    natCast_mul_le_iff hs]

end MMP.Resolution

end
