module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.SNCPullback
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.Morphisms.Smooth.IrreducibleComponents
import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientPowers
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatDescent
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatBaseChange
import MMP.AlgebraicGeometry.Resolution.Blowup.StrictTransform
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MaxOrderControlledTransform
import MMP.AlgebraicGeometry.Resolution.OrderReduction.TuningOfIdeals
import MMP.AlgebraicGeometry.Resolution.MaximalContact.OnePlusBInvariance
import MMP.AlgebraicGeometry.Resolution.LinearBlowupCharts
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Resolution.OrderReduction.OrderMSequenceCosupport
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MixedIdealMonomialReduction
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MarkedMixedIdealStep
import MMP.AlgebraicGeometry.Resolution.OrderReduction.Existence
import MMP.AlgebraicGeometry.Resolution.OrderReduction.IdealFunctor
import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealTransform
import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientIdeal

/-!
# The canonical marked order reduction without a divisor, and closed embeddings

Let `𝓑` be an order-reduction family on dimensions `a, …, b` and `(X, I, ∅)` a triple with
`dim X = d ∈ [a, b]` and `m = maxord I ≥ 1`. Then the functor `𝓑𝓜𝓞_{d,m}[𝓑]` applied to the
marked triple `(X, I, m, ∅)` is the sequence `𝓑_{d,m}(X, I, ∅)`: with `E = ∅` the monomial part
of `I` is trivial, so Step 1 of the construction is the single round `𝓑_{d,m}(X, I, ∅)`, after
which the maximal order is `< m`, and Steps 2 and 3 are empty. Applied to the order-reduction
family `(𝓑𝓞_d)_d` from which the canonical `𝓑𝓜𝓞` is built, this gives
`𝓑𝓜𝓞_{n,m}(X, I, m, ∅) = 𝓑𝓞_{n,m}(X, I, ∅)`.

Let `τ : Y ↪ X` be a closed embedding of smooth equidimensional schemes of finite type over a
field `k` of characteristic `0`, `J ⊆ 𝒪_Y` an ideal sheaf nonzero at the generic point of every
irreducible component of `Y`, and `I ⊆ 𝒪_X` the ideal with `τ_*(𝒪_Y/J) = 𝒪_X/I`. Then
`𝓑𝓜𝓞_{dim X,1}(X, I, 1, ∅)` is the push-forward along `τ` of `𝓑𝓜𝓞_{dim Y,1}(Y, J, 1, ∅)`; that
is, the canonical `𝓑𝓜𝓞_1` has the closed embedding property used by the principalization
construction of Kollár 3.72.

The closed embedding statement is proved by induction on `dim X`; write `𝓑𝓜𝓞(·)` for
`𝓑𝓜𝓞_{dim(·),1}(·, ·, 1, ∅)`. If `dim X = dim Y`, then `Y` is open and closed in `X` (the
components of the smooth scheme `X` are open and pairwise disjoint), `τ` is an open immersion,
and since `𝓑𝓜𝓞` commutes with the open immersions `Y ⊆ X` and `X ∖ Y ⊆ X` and `I = 𝒪_X` off `Y`,
`𝓑𝓜𝓞(Y)` is the restriction of `𝓑𝓜𝓞(X)` step by step. If `dim X > dim Y`, the ideal of `Y` has
order `1` along `Y`, so on a finite disjoint union `g : X^* → X` of affine opens there is a
smooth hypersurface `H ⊇ Y^* = Y ×_X X^*`. By induction `𝓑𝓜𝓞(H, I_H)` is the push-forward of
`𝓑𝓜𝓞(Y^*)`, and by Kollár Thm. 3.103 (3) `𝓑𝓜𝓞(X^*) = 𝓑𝓞(X^*)` is the push-forward of
`𝓑𝓜𝓞(H, I_H)`. Push-forwards compose, `𝓑𝓜𝓞` commutes with the surjective open cover maps `g` and
`Y^* → Y`, and push-forwards descend along flat surjections.

## Main results

* `MMP.Resolution.bmoFunctor_eq_of_maxOrder_eq`: `𝓑𝓜𝓞_{d,m}[𝓑](X, I, m, ∅) = 𝓑_{d,m}(X, I, ∅)`.
* `MMP.Resolution.bmoFamily_eq_boFamily_of_maxOrder_eq`: the same for the canonical families.
* `MMP.Resolution.isPushforward_bmoFamily_of_closedEmbedding`: the canonical `𝓑𝓜𝓞_{·,1}`
  commutes with closed embeddings.
* `MMP.Resolution.hasClosedEmbeddingProperty_bmoFamily`: the same, as
  `HasClosedEmbeddingProperty`.

## Implementation notes

In `isPushforward_bmoFamily_of_closedEmbedding` the ideal `I` is not assumed nonzero on the
components of `X`: this follows from `I ⊇ I_Y` and `I = 𝒪_X` off `Y`. The conclusion is the
push-forward relation `ClosedBlowupSequence.IsPushforward`, which says that the centres on `X`
are the images of the centres on `Y` step by step; this is the form of
`HasClosedEmbeddingProperty`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.70, Claims 3.71.1 and 3.71.2, 3.72,
  Thm. 3.107(3), 3.108 and 3.111]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-- A scheme of dimension `n` has dimension index `dimNat X = n`. -/
private theorem dimNat_eq {X : Scheme.{u}} {n : ℕ}
    (h : topologicalKrullDim X = ((n : ℕ∞) : WithBot ℕ∞)) : dimNat X = n := by
  simp [dimNat, h]

/-- A scheme with a dimension in `N` has its dimension index in `N`. -/
private lemma dimNat_mem_of_hasDimensionIn {X : Scheme.{u}} {N : Set ℕ} (h : HasDimensionIn X N) :
    dimNat X ∈ N := by
  obtain ⟨n, hn, hX⟩ := h
  rwa [dimNat_eq hX]

/-- The order of an ideal sheaf at a point is at most its maximal order. -/
private theorem multAt_le_maxOrder {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    multAt I x ≤ maxOrder I :=
  le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) x (Set.mem_univ x)

/-! ### `𝓑𝓜𝓞_{d,m}[𝓑]` without a divisor -/

/-- With no divisor the nonmonomial part of `I` is `I`. -/
private theorem nonmonomialPart_empty {X : Scheme.{u}} (I : X.IdealSheafData) :
    nonmonomialPart I (OrderedDivisor.empty X) = I := by
  have hA : monomialPartCoeff I (OrderedDivisor.empty X) = 0 := by
    funext D
    simp [monomialPartCoeff, OrderedDivisor.IsComponent, OrderedDivisor.empty]
  have hM : monomialPart I (OrderedDivisor.empty X) = ⊤ := by
    rw [monomialPart, hA, divisorIdeal]
    simp only [Pi.zero_apply, pow_zero]
    exact (finprod_one).trans Scheme.IdealSheafData.one_eq_top
  rw [nonmonomialPart, hM]
  refine le_antisymm (fun V x hx => ?_) (le_idealColon _ _)
  have h := Scheme.IdealSheafData.ideal_ofIdeals_le _ V hx
  rw [Submodule.mem_colon] at h
  simpa using h 1 (by simp)

/-- An ideal of a local ring lies in the power of the maximal ideal given by its order. -/
private theorem le_maximalIdeal_pow_toNat_idealOrder {R : Type*} [CommRing R] [IsLocalRing R]
    (J : Ideal R) : J ≤ IsLocalRing.maximalIdeal R ^ (idealOrder J).toNat := by
  by_cases htop : idealOrder J = ⊤
  · simp [htop]
  · set n := (idealOrder J).toNat with hn
    have hord : idealOrder J = (n : ℕ∞) := (ENat.coe_toNat htop).symm
    by_contra hnle
    have hn0 : n ≠ 0 := by
      rintro h0
      exact hnle (by simp [h0])
    have : idealOrder J ≤ ((n - 1 : ℕ) : ℕ∞) := by
      refine iSup₂_le fun j hj => ?_
      have : j < n := by
        by_contra hjn
        exact hnle (hj.trans (Ideal.pow_le_pow_right (not_lt.mp hjn)))
      exact_mod_cast Nat.le_sub_one_of_lt this
    rw [hord] at this
    have : n ≤ n - 1 := by exact_mod_cast this
    omega

/-- No set is an irreducible component of two distinct members of an snc family through a point
of it: both members would be cut out at that point by the same member of a regular system of
parameters. -/
private theorem false_of_mem_componentsOf_of_ne {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] {sY : Y ⟶ Spec (.of k)} {s : ℕ} {F : Fin s → Y.IdealSheafData}
    (hF : IsSNCFamily sY F) {W : Set Y} {a b : Fin s} (hab : a ≠ b)
    (ha : W ∈ componentsOf ((F a).support : Set Y)) (hb : W ∈ componentsOf ((F b).support : Set Y))
    {x : Y} (hxW : x ∈ W) : False := by
  obtain ⟨n, z, c, hz, hst, hc⟩ := hF.2 x
  let ia := c ⟨a, ha.1.2 hxW⟩
  let ib := c ⟨b, hb.1.2 hxW⟩
  have hne : ib ≠ ia := fun h => hab (congrArg Subtype.val (hc h)).symm
  have hJ : ∀ (j : Fin s) (hj : x ∈ ((F j).support : Set Y)),
      IdealSheafData.stalk (F j) x = (coordPrime hz {c ⟨j, hj⟩}).asIdeal := by
    intro j hj
    rw [hst ⟨j, hj⟩]
    simp [coordPrime]
  have hWa := eq_closure_coordPrime_of_mem_componentsOf hz (hJ a (ha.1.2 hxW)) ha hxW
  have hWb := eq_closure_coordPrime_of_mem_componentsOf hz (hJ b (hb.1.2 hxW)) hb hxW
  have hle : (coordPrime hz {ia}).asIdeal ≤ (coordPrime hz {ib}).asIdeal := by
    rw [← fromSpecStalk_mem_closure_iff, ← hWa, hWb]
    exact subset_closure rfl
  have hsp : ∀ i : Fin n, (coordPrime hz {i}).asIdeal = Ideal.span {z i} := fun i => by
    simp [coordPrime]
  rw [hsp, hsp] at hle
  exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hne
    (hle (Ideal.subset_span rfl))

/-- For a triple `(X, I, E)` and an open `U ⊆ X`, every weight `σ_J(x)` of the monomial data
`(U, E|_U, A(I|_U))` at a point `x ∈ E^J ∩ U` is at most `ord_x I`: the divisors through `x` that
are components of the `E_j`, `j ∈ J`, are distinct, and `I|_U` lies in the product of their
powers `D^{A(D)}`. -/
private theorem stratumWeight_le_multAt {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X)
    (ht : IsTriple sX I E) (U : X.Opens) (J : Finset (Fin (E.comap U.ι).s)) (x : U)
    (hx : x ∈ (⟨k, U.ι ≫ sX, E.comap U.ι, monomialPartCoeff (I.comap U.ι) (E.comap U.ι)⟩ :
      MonomialData U).stratum J) :
    (⟨k, U.ι ≫ sX, E.comap U.ι, monomialPartCoeff (I.comap U.ι) (E.comap U.ι)⟩ :
      MonomialData U).stratumWeight J x ≤ multAt I (U.ι x) := by
  classical
  obtain ⟨hk, hsm, hlft, -, -, -, hE⟩ := ht
  have := hk
  have := hlft
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  have : Smooth sX := Aux.smooth_of_isSmoothScheme' sX hsm
  have : LocallyOfFinitePresentation (U.ι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := U.ι ≫ sX)).mpr inferInstance
  have hsmU : MMP.Mori.IsSmoothScheme (U.ι ≫ sX) :=
    (MMP.Mori.isSmoothScheme_iff _).2 inferInstance
  have hEU : IsSNCFamily (U.ι ≫ sX) (E.comap U.ι).E :=
    isSNCFamily_comap_of_flat sX (U.ι ≫ sX) U.ι (fun y => Flat.stalkMap U.ι y)
      (fun y => MMP.Resolution.isRegularLocalRing_closedFibre_of_smooth U.ι y) hE.2
  set I' := I.comap U.ι
  set A' := monomialPartCoeff I' (E.comap U.ι)
  let f : Fin (E.comap U.ι).s → AlgebraicGeometry.PrimeDivisor U → ℕ := fun j D =>
    if D.support ∈ componentsOf (((E.comap U.ι).E j).support : Set U) ∧ x ∈ (D.support : Set U)
    then A' D else 0
  let F : Fin (E.comap U.ι).s → Finset (AlgebraicGeometry.PrimeDivisor U) := fun j =>
    if h : (Function.support (f j)).Finite then h.toFinset else ∅
  have hcoeff : ∀ j, (⟨k, U.ι ≫ sX, E.comap U.ι, A'⟩ : MonomialData U).coeffAt j x =
      ∑ D ∈ F j, f j D := by
    intro j
    change ∑ᶠ D, f j D = _
    by_cases h : (Function.support (f j)).Finite
    · simp only [F, dif_pos h]
      exact finsum_eq_sum_of_support_subset _ (by simp)
    · simp only [F, dif_neg h, Finset.sum_empty]
      exact finsum_of_infinite_support h
  set T := J.biUnion F
  have hT : ∀ D ∈ T, x ∈ (D.support : Set U) := by
    intro D hD
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hD
    by_cases h : (Function.support (f j)).Finite
    · simp only [F, dif_pos h, Set.Finite.mem_toFinset, Function.mem_support] at hj
      by_contra hx
      exact hj (by simp [f, hx])
    · simp [F, dif_neg h] at hj
  have hσ : (⟨k, U.ι ≫ sX, E.comap U.ι, A'⟩ : MonomialData U).stratumWeight J x ≤
      ∑ D ∈ T, A' D := by
    unfold MonomialData.stratumWeight
    rw [Finset.sum_congr rfl fun j _ => hcoeff j]
    refine (Finset.sum_le_sum fun j hj =>
      Finset.sum_le_sum_of_subset (Finset.subset_biUnion_of_mem F hj)).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun D _ => ?_
    by_cases hex : ∃ j ∈ J, D.support ∈ componentsOf (((E.comap U.ι).E j).support : Set U) ∧
        x ∈ (D.support : Set U)
    · obtain ⟨j₀, hj₀, hc₀⟩ := hex
      rw [Finset.sum_eq_single j₀]
      · simp [f, hc₀]
      · intro j _ hj
        simp only [f]
        refine if_neg fun h => ?_
        exact false_of_mem_componentsOf_of_ne hEU hj h.1 hc₀.1 h.2
      · exact fun h => absurd hj₀ h
    · push Not at hex
      rw [Finset.sum_eq_zero fun j hj => ?_]
      · exact Nat.zero_le _
      · simp only [f]
        exact if_neg fun h => hex j hj h.1 h.2
  have hle : I' ≤ ∏ D ∈ T, D.idealSheaf ^ A' D := by
    refine Aux.le_prod_of_stalk_le (U.ι ≫ sX) hsmU A' T I' fun D _ => ?_
    by_cases hc : (E.comap U.ι).IsComponent D
    · have hA : A' D = (idealOrder (IdealSheafData.stalk I' D.genericPoint)).toNat := by
        simp [A', monomialPartCoeff, hc, multAt]
      rw [hA]
      exact le_maximalIdeal_pow_toNat_idealOrder _
    · have : A' D = 0 := by simp [A', monomialPartCoeff, hc]
      simp [this]
  have hord : ((∑ D ∈ T, A' D : ℕ) : ℕ∞) ≤ multAt I' x := by
    unfold multAt idealOrder
    refine le_iSup₂_of_le (∑ D ∈ T, A' D) ?_ le_rfl
    refine (stalk_le_stalk_of_le hle x).trans ?_
    refine (Aux.stalk_prod T (fun D => D.idealSheaf ^ A' D)
      (show (U : Scheme.{u}) from x)).le.trans ?_
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod' fun D hD => ?_
    refine (Aux.stalk_pow D.idealSheaf (A' D) (show (U : Scheme.{u}) from x)).le.trans ?_
    refine Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal fun htop => ?_) _
    exact (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).1 htop (hT D hD)
  exact (Nat.cast_le.2 hσ).trans (le_multAt_of_le_multAt_comap U.ι I x hord)

/-- The monomial order reduction from step `r` is empty when every `m_s`, `s ≥ r`, is `< m`. -/
private theorem monomialOrderReductionFrom_eq_nil (m : ℕ) :
    ∀ (j r : ℕ) {X : Scheme.{u}} (C : MonomialData X), (∀ s, C.maxStratumWeight s < m) →
      MonomialData.monomialOrderReductionFrom m j r C = .nil X
  | 0, _, _, _, _ => rfl
  | j + 1, r, X, C, h => by
    have hex : ∃ N, ((C.iterate m r N).2.maxStratumWeight r) < m := ⟨0, h r⟩
    rw [MonomialData.monomialOrderReductionFrom, dif_pos hex,
      (Nat.find_eq_zero hex).2 (h r)]
    exact monomialOrderReductionFrom_eq_nil m j (r + 1) C h

/-- The monomial order reduction of the Step-3 data is empty when the maximal order is `< m`. -/
private theorem monomialOrderReduction_eq_nil {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X)
    (ht : IsTriple sX I E) {m : ℕ} (hm : 1 ≤ m) (hlt : maxOrder I < m) (U : X.Opens) :
    (⟨k, U.ι ≫ sX, E.comap U.ι, monomialPartCoeff (I.comap U.ι) (E.comap U.ι)⟩ :
      MonomialData U).monomialOrderReduction m = .nil U := by
  refine monomialOrderReductionFrom_eq_nil m _ _ _ fun r => ?_
  have hle : ∀ J x, x ∈ (⟨k, U.ι ≫ sX, E.comap U.ι,
      monomialPartCoeff (I.comap U.ι) (E.comap U.ι)⟩ : MonomialData U).stratum J →
      (⟨k, U.ι ≫ sX, E.comap U.ι, monomialPartCoeff (I.comap U.ι) (E.comap U.ι)⟩ :
        MonomialData U).stratumWeight J x ≤ m - 1 := fun J x hx => by
    have : (_ : ℕ∞) < m := ((stratumWeight_le_multAt sX I E ht U J x hx).trans
      (multAt_le_maxOrder I _)).trans_lt hlt
    exact Nat.le_sub_one_of_lt (by exact_mod_cast this)
  refine Nat.lt_of_le_sub_one hm ?_
  unfold MonomialData.maxStratumWeight
  exact ciSup_le' fun J => ciSup_le' fun _ => ciSup_le' fun x => ciSup_le' fun hx => hle J x hx

/-- The maximal order of the nonmonomial part is at most that of the ideal. -/
private theorem maxOrder_nonmonomialPart_le {X : Scheme.{u}} (I : X.IdealSheafData)
    (E : OrderedDivisor X) : maxOrder (nonmonomialPart I E) ≤ maxOrder I :=
  iSup₂_mono fun z _ => Kollar.multAt_antitone (le_idealColon _ _) z

/-- Appending the empty sequence does nothing. -/
private theorem append_nil {X : Scheme.{u}} :
    ∀ S : ClosedBlowupSequence X, S.append (.nil S.target) = S
  | .nil _ => rfl
  | .cons Z S => congrArg (ClosedBlowupSequence.cons Z) (append_nil S)

/-- The rounds of Step 1 stop at once when the nonmonomial part has maximal order `< m`. -/
private theorem bmoStepOneAux_eq_nil (B : UnmarkedFamily.{u}) (d m : ℕ) :
    ∀ (q : ℕ) (t : MarkedTriple.{u}), maxOrder (nonmonomialPart t.I t.E) < m →
      bmoStepOneAux B d m q t = .nil t.X
  | 0, _, _ => rfl
  | q + 1, t, h => by rw [bmoStepOneAux, if_pos h]

/-- The Step-3 monomial order reduction at the end `(X, I, m, E)` of the empty sequence is
empty when `maxord I < m`. -/
private theorem monomialOrderReduction_endOf_nil_eq_nil (s : MarkedTriple.{u})
    (hs : IsTriple s.sX s.I s.E) {m : ℕ} (hm : 1 ≤ m) (hlt : maxOrder s.I < m) :
    (⟨(s.endOf m (.nil s.X)).k,
      Scheme.Opens.ι (nonmonomialPart (s.endOf m (.nil s.X)).I
        (s.endOf m (.nil s.X)).E).support.compl ≫ (s.endOf m (.nil s.X)).sX,
      (s.endOf m (.nil s.X)).E.comap (Scheme.Opens.ι
        (nonmonomialPart (s.endOf m (.nil s.X)).I (s.endOf m (.nil s.X)).E).support.compl),
      monomialPartCoeff ((s.endOf m (.nil s.X)).I.comap (Scheme.Opens.ι
          (nonmonomialPart (s.endOf m (.nil s.X)).I (s.endOf m (.nil s.X)).E).support.compl))
        ((s.endOf m (.nil s.X)).E.comap (Scheme.Opens.ι (nonmonomialPart
          (s.endOf m (.nil s.X)).I (s.endOf m (.nil s.X)).E).support.compl))⟩ :
      MonomialData _).monomialOrderReduction m = .nil _ :=
  monomialOrderReduction_eq_nil (𝟙 s.X ≫ s.sX) s.I s.E (by rwa [Category.id_comp]) hm
    hlt _

/-- The end of a sequence of order `≥ m` starting with a marked triple is a triple. -/
private theorem isTriple_end {k : Type u} [Field k] {X : Scheme.{u}} :
    ∀ (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), S.IsOrderGeMarkedTripleSeq s a E →
      IsTriple (S.toBase ≫ s) (S.markedTransform a).I (S.orderedTotalTransform E)
  | .nil X, s, a, E, h => by
    show IsTriple (𝟙 X ≫ s) a.I E
    rwa [Category.id_comp]
  | .cons Z S, s, a, E, h => by
    show IsTriple ((S.toBase ≫ blowUpToBase Z) ≫ s) _ _
    rw [Category.assoc]
    exact isTriple_end S _ _ _ h.2.2.2.2.2

/-- **`𝓑𝓜𝓞` reduces to `𝓑` without a divisor** (Kollár Thm. 3.107(3)). Let `𝓑` be an
order-reduction family on dimensions `a, …, b` (`IsOrderReductionFamily`) and `(X, I, ∅)` a
triple with `dim X = d`, `a ≤ d ≤ b` and `maxord I = m ≥ 1`. Then
`bmoFunctor B d m (X, I, m, ∅) = B d m (X, I, ∅)`. -/
@[mmp "thm_kr3e_bmo_eq_bo"]
public theorem bmoFunctor_eq_of_maxOrder_eq {a b d m : ℕ} (B : UnmarkedFamily.{u})
    (hB : IsOrderReductionFamily a b B) (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hE : t.E = OrderedDivisor.empty t.X)
    (hdim : topologicalKrullDim t.X = ((d : ℕ∞) : WithBot ℕ∞)) (hd : d ∈ Set.Icc a b)
    (hmax : maxOrder t.I = m) (hm : 1 ≤ m) :
    bmoFunctor B d m (⟨t, m⟩ : MarkedTriple.{u}) = B d m t := by
  have htT : IsTriple t.sX t.I t.E := ht
  obtain ⟨F, hFB, hFred⟩ := hB m hm
  have hdn : dimNat t.X = d := dimNat_eq hdim
  have htC : t ∈ idealTriplesOfDim (Set.Icc a b) m := ⟨ht, ⟨d, hd, hdim⟩, hmax.le⟩
  have hS : F.toFun t htC = B d m t := by rw [hFB, hdn]
  have hseq := F.isOrderMTripleSeq t htC
  have hne := F.hasNoEmptyBlowups t htC
  have hlt := hFred.1 t htC
  rw [hS] at hseq hne hlt
  have hmk := ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX t.I t.E
    htT m hmax (B d m t)
  have hge := hmk.1.2 hseq
  have hlt1 : maxOrder ((B d m t).markedTransform ⟨t.I, m⟩).I < m := by rwa [hmk.2 hseq]
  have hN : nonmonomialPart t.I t.E = t.I := by rw [hE]; exact nonmonomialPart_empty _
  have hstep1 : bmoStepOne B d m (⟨t, m⟩ : MarkedTriple.{u}) = B d m t := by
    change bmoStepOneAux B d m ((maxOrder (nonmonomialPart t.I t.E)).toNat + 1) ⟨t, m⟩ = _
    rw [bmoStepOneAux, if_neg (by rw [hN, hmax]; exact lt_irrefl _)]
    dsimp only
    rw [hN, hmax, ENat.toNat_coe]
    refine (congrArg (ClosedBlowupSequence.append (B d m t)) ?_).trans (append_nil _)
    classical
    refine ite_eq_iff'.2 ⟨fun _ => ?_, fun _ => rfl⟩
    exact bmoStepOneAux_eq_nil _ _ _ _ _ ((maxOrder_nonmonomialPart_le _ _).trans_lt
      hlt1)
  have htm : (⟨t, m⟩ : MarkedTriple.{u}) ∈ markedTriples := ht
  have hstep2 : bmoStepTwo B d m ((⟨t, m⟩ : MarkedTriple.{u}).endOf m (B d m t)) = .nil _ := by
    have h0 : bmoStepTwoOrder m ((⟨t, m⟩ : MarkedTriple.{u}).endOf m (B d m t)) = 0 := by
      unfold bmoStepTwoOrder
      have hc : (⟨((⟨t, m⟩ : MarkedTriple.{u}).endOf m (B d m t)).I, m⟩ :
          MarkedIdeal _).cosupport = ∅ := by
        ext x
        simp only [MarkedIdeal.cosupport, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_le]
        exact (multAt_le_maxOrder _ x).trans_lt hlt1
      rw [hc, maxOrderAlong]
      simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot]
      rfl
    unfold bmoStepTwo
    rw [h0, bmoStepTwoAux, if_pos h0]
  classical
  unfold bmoFunctor
  dsimp only
  rw [if_pos htm, hstep1]
  have hS2 : (if (⟨t, m⟩ : MarkedTriple.{u}).endOf m (B d m t) ∈ markedTriples then
      bmoStepTwo B d m ((⟨t, m⟩ : MarkedTriple.{u}).endOf m (B d m t)) else .nil _) = .nil _ := by
    split_ifs
    · exact hstep2
    · rfl
  rw [hS2, monomialOrderReduction_endOf_nil_eq_nil _
    (isTriple_end (B d m t) t.sX ⟨t.I, m⟩ t.E hge) hm hlt1]
  change ((B d m t).append (.nil _)).reduction = _
  rw [append_nil]
  exact ClosedBlowupSequence.reduction_eq_self hne

/-! ### `bmoFunctor B d` only reads `B` in dimension `d` -/

/-- The rounds of Step 1 of `𝓑𝓜𝓞_d[𝓑]` only read `𝓑` in dimension `d`. -/
private lemma bmoStepOneAux_eq_const (B : UnmarkedFamily.{u}) (d m q : ℕ) :
    bmoStepOneAux B d m q = bmoStepOneAux (fun _ => B d) d m q := by
  induction q with
  | zero => rfl
  | succ q ih => funext t; simp only [bmoStepOneAux, ih]

/-- The rounds of Step 2 of `𝓑𝓜𝓞_d[𝓑]` only read `𝓑` in dimension `d`. -/
private lemma bmoStepTwoAux_eq_const (B : UnmarkedFamily.{u}) (d m q : ℕ) :
    bmoStepTwoAux B d m q = bmoStepTwoAux (fun _ => B d) d m q := by
  induction q with
  | zero => rfl
  | succ q ih => funext t; simp only [bmoStepTwoAux, ih]

/-- `𝓑𝓜𝓞_d[𝓑]` only reads `𝓑` in dimension `d`. -/
private lemma bmoFunctor_eq_const (B : UnmarkedFamily.{u}) (d : ℕ) :
    bmoFunctor B d = bmoFunctor (fun _ => B d) d := by
  funext m t
  unfold bmoFunctor bmoStepOne bmoStepTwo
  rw [funext (bmoStepOneAux_eq_const B d m), funext (bmoStepTwoAux_eq_const B d m)]

/-- Families agreeing in dimension `d` give the same `𝓑𝓜𝓞_d`. -/
private lemma bmoFunctor_congr {B B' : UnmarkedFamily.{u}} {d : ℕ} (h : B d = B' d) :
    bmoFunctor B d = bmoFunctor B' d := by
  rw [bmoFunctor_eq_const B, bmoFunctor_eq_const B', h]

/-! ### `boFunctor M n` only reads `M` in dimension `n - 1` -/

/-- The divisor separation rounds on `X` only read `M` in dimension `dim X - 1`. -/
private lemma divisorSeparationAux_eq_const (M : MarkedFamily.{u}) (m : ℕ)
    (t : FieldBlowupTriple.{u}) (j : ℕ) :
    divisorSeparationAux M m t j = divisorSeparationAux (fun _ => M (dimNat t.X - 1)) m t j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [divisorSeparationAux]
    generalize divisorSeparationAux M m t j = P at ih ⊢
    subst ih
    rfl

open Classical in
/-- The body of `boMaximalContact`, as a function of the divisor separation sequence `P` and of
the functor `bd` applied on the complement of the old divisors. -/
private noncomputable def boMaximalContactOfSeq (t : FieldBlowupTriple.{u})
    (H : t.X.IdealSheafData) (P : ClosedBlowupSequence t.X)
    (bd : (t : FieldBlowupTriple.{u}) → ClosedBlowupSequence t.X) : ClosedBlowupSequence t.X :=
  let t' := t.endOf P
  let H' : t'.X.IdealSheafData := (P.restrictHom H).ker
  let V : t'.X.Opens :=
    (⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥).compl
  let EV : OrderedDivisor V :=
    ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
      fun i => (t'.E.E ⟨t.E.s + i, by omega⟩).comap V.ι⟩
  let tV : FieldBlowupTriple.{u} := ⟨⟨V, t'.I.comap V.ι, EV⟩, t'.k, V.ι ≫ t'.sX⟩
  let BV : ClosedBlowupSequence V :=
    if (V : Set t'.X).Nonempty ∧ IsTriple tV.sX tV.I tV.E then bd tV else .nil _
  (P.append (BV.extendByClosure V.ι)).reduction

/-- `boMaximalContact` unfolded through `boMaximalContactOfSeq`. -/
private lemma boMaximalContact_eq_ofSeq (M : MarkedFamily.{u}) (m : ℕ) (t : FieldBlowupTriple.{u})
    (H : t.X.IdealSheafData) :
    boMaximalContact M m t H =
      boMaximalContactOfSeq t H (divisorSeparationSequence M m t) (bdFunctor M (dimNat t.X) m 0) :=
  rfl

/-- `boMaximalContact M m t` only reads `M` in dimension `dim X - 1`. -/
private lemma boMaximalContact_eq_const (M : MarkedFamily.{u}) (m : ℕ) (t : FieldBlowupTriple.{u})
    (H : t.X.IdealSheafData) :
    boMaximalContact M m t H = boMaximalContact (fun _ => M (dimNat t.X - 1)) m t H := by
  rw [boMaximalContact_eq_ofSeq, boMaximalContact_eq_ofSeq,
    show divisorSeparationSequence M m t =
      divisorSeparationSequence (fun _ => M (dimNat t.X - 1)) m t from
    divisorSeparationAux_eq_const M m t t.E.s]
  rfl

/-- Marked families agreeing in dimension `dim X - 1` give the same `boLocal` on `X`. -/
private lemma boLocal_congr {M M' : MarkedFamily.{u}} (m : ℕ) (t : FieldBlowupTriple.{u})
    (h : M (dimNat t.X - 1) = M' (dimNat t.X - 1)) :
    boLocal M m t = boLocal M' m t := by
  unfold boLocal
  rw [boMaximalContact_eq_const M, boMaximalContact_eq_const M']
  dsimp only
  rw [h]

/-- Marked families agreeing in dimension `n - 1` give the same `𝓑𝓞_n`. -/
private lemma boFunctor_congr {M M' : MarkedFamily.{u}} {n : ℕ} (h : M (n - 1) = M' (n - 1)) :
    boFunctor M n = boFunctor M' n := by
  funext m t
  have key : ∀ t' : FieldBlowupTriple.{u}, t' ∈ mcLocalTriples n m →
      boLocal M m t' = boLocal M' m t' := fun t' ht' =>
    boLocal_congr m t' (by rwa [dimNat_mem_of_hasDimensionIn ht'.2.1])
  unfold boFunctor
  congr! 10 <;> rename_i h3 <;> rw [key _ h3]

/-! ### `boFamily` is an order-reduction family -/

/-- Being an order-reduction family on `a, …, b` only depends on those dimensions. -/
private lemma isOrderReductionFamily_congr {a b : ℕ} {B B' : UnmarkedFamily.{u}}
    (h : ∀ d, a ≤ d → d ≤ b → B d = B' d) (hB : IsOrderReductionFamily a b B) :
    IsOrderReductionFamily a b B' := by
  intro μ hμ
  obtain ⟨F, hF, hF'⟩ := hB μ hμ
  refine ⟨F, fun t ht => ?_, hF'⟩
  obtain ⟨h1, h2⟩ := dimNat_mem_of_hasDimensionIn ht.2.1
  rw [hF, h _ h1 h2]

/-- `bmoFamily` ignores empty entries on the marked triples of marking `μ` and dimension `d`. -/
private lemma ignoresEmptyEntriesMarked_bmoFamily_of_dim {d μ : ℕ} (hμ : 1 ≤ μ) :
    IgnoresEmptyEntriesMarked (markedTriplesOfDim.{u} {d} μ) (fun t _ => bmoFamily d μ t) := by
  intro t ht
  obtain ⟨h, he⟩ := ignoresEmptyEntriesMarked_bmoFamily hμ t ⟨ht.1, ht.2.1⟩
  refine ⟨⟨h.1, ht.2.1, ht.2.2⟩, ?_⟩
  have hd : dimNat t.X = d := dimNat_mem_of_hasDimensionIn ht.2.2
  have he' : bmoFamily (dimNat t.X) μ t.deleteEmpty = bmoFamily (dimNat t.X) μ t := he
  rwa [hd] at he'

/-- `boFamily` is an order-reduction family on dimensions `0, …, n + 1`. -/
private lemma isOrderReductionFamily_boFamily (n : ℕ) :
    IsOrderReductionFamily.{u} 0 (n + 1) boFamily := by
  refine isOrderReductionFamily_congr (fun d _ hd => ?_)
    ((isOrderReductionFamily_boFunctor (Nat.succ_pos n)).1 bmoFamily
      (isMarkedOrderReductionFamily_bmoFamily n)
      (fun d _ μ hμ => ignoresEmptyEntriesMarked_bmoFamily_of_dim hμ))
  rcases d with _ | e
  · funext μ t; rfl
  · funext μ t
    simp only [Nat.add_one_ne_zero, ↓reduceIte, boFamily, boFamilyUpTo,
      show ¬ e + 1 ≤ e by omega]
    rw [boFunctor_congr (M' := bmoFamilyOf (boFamilyUpTo e) e)]
    funext μ' t'
    simp [bmoFamilyOf, bmoFamily]

/-! ### The canonical `𝓑𝓜𝓞_{n,m}` without a divisor -/

/-- **The canonical `𝓑𝓜𝓞` reduces to `𝓑𝓞` without a divisor** (Kollár Claim 3.71.1). For a
triple `(X, I, ∅)` with `dim X = n` and `maxord I = m ≥ 1`,
`bmoFamily n m (X, I, m, ∅) = boFamily n m (X, I, ∅)`. -/
@[mmp "thm_kr3e_bmo_eq_bo_family"]
public theorem bmoFamily_eq_boFamily_of_maxOrder_eq {n m : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (hE : t.E = OrderedDivisor.empty t.X)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞))
    (hmax : maxOrder t.I = m) (hm : 1 ≤ m) :
    bmoFamily n m (⟨t, m⟩ : MarkedTriple.{u}) = boFamily n m t := by
  have h : bmoFamily.{u} n = bmoFunctor boFamily n :=
    bmoFunctor_congr (by funext μ s; simp [UnmarkedFamily.truncate, boFamily])
  rw [h]
  exact bmoFunctor_eq_of_maxOrder_eq boFamily (isOrderReductionFamily_boFamily n) t ht hE hdim
    ⟨Nat.zero_le n, Nat.le_succ n⟩ hmax hm

/-! ### Closed embeddings -/

set_option backward.isDefEq.respectTransparency false in
/-- An open cover map is smooth. -/
private theorem smooth_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) : Smooth g := by
  obtain ⟨n, U, -, hU, hi⟩ := hg
  exact IsZariskiLocalAtSource.of_iSup_eq_top U hU fun a => inferInstance

/-- The base change of an open cover map is an open cover map. -/
private theorem isOpenCoverMap_of_isPullback {X Y Y' S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) (hg : IsOpenCoverMap g) :
    IsOpenCoverMap g' := by
  obtain ⟨n, U, hd, hU, hi⟩ := hg
  refine ⟨n, fun a => f' ⁻¹ᵁ U a, fun a b hab => ?_, ?_, fun a => ?_⟩
  · change Disjoint _ _
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.1 (hd hab),
      Scheme.Hom.preimage_bot]
  · rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  · have hpb := (isPullback_morphismRestrict f' (U a)).flip.paste_horiz sq.flip
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip (hi a)

/-- An open cover map, with the pieces indexed by a finite type. -/
private theorem isOpenCoverMap_of_finite {X' X : Scheme.{u}} {g : X' ⟶ X} {ι : Type*} [Finite ι]
    (U : ι → X'.Opens) (hd : Pairwise (fun a b => Disjoint (U a) (U b))) (hU : (⨆ a, U a) = ⊤)
    (hi : ∀ a, IsOpenImmersion ((U a).ι ≫ g)) : IsOpenCoverMap g := by
  let e := Finite.equivFin ι
  refine ⟨Nat.card ι, fun a => U (e.symm a), fun a b hab => hd (e.symm.injective.ne hab),
    ?_, fun a => hi _⟩
  rw [← hU]
  exact e.symm.iSup_comp (g := U)

/-- The order is invariant under a bijective ring map of local rings. -/
private theorem idealOrder_map_of_bijective {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) (hφ : Function.Bijective φ) (J : Ideal R) :
    idealOrder (J.map φ) = idealOrder J := by
  let e : R ≃+* S := RingEquiv.ofBijective φ hφ
  have hm : (IsLocalRing.maximalIdeal R).map e = IsLocalRing.maximalIdeal S :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  have key : ∀ j : ℕ, J.map φ ≤ IsLocalRing.maximalIdeal S ^ j ↔
      J ≤ IsLocalRing.maximalIdeal R ^ j := by
    intro j
    change J.map e ≤ _ ↔ _
    rw [← hm, ← Ideal.map_pow, Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _
      e.bijective]
  simp only [idealOrder, key]

/-- The order of an ideal sheaf is preserved by pull-back along an open immersion. -/
private theorem multAt_comap_of_isOpenImmersion {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)
    [IsOpenImmersion f] (J : Y.IdealSheafData) (y : Y') :
    multAt (J.comap f) y = multAt J (f y) := by
  rw [multAt, IdealSheafData.stalk_comap,
    idealOrder_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]
  rfl

/-- The order of an ideal sheaf is preserved by pull-back along an open cover map. -/
private theorem multAt_comap_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (I : X.IdealSheafData) (y : X') :
    multAt (I.comap g) y = multAt I (g y) := by
  obtain ⟨n, U, -, hU, hi⟩ := hg
  have hy : y ∈ ⨆ a, U a := hU ▸ trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  have h1 := multAt_comap_of_isOpenImmersion (U a).ι (I.comap g) ⟨y, ha⟩
  have h2 := multAt_comap_of_isOpenImmersion ((U a).ι ≫ g) I ⟨y, ha⟩
  rw [Scheme.IdealSheafData.comap_comp] at h2
  rw [h2] at h1
  exact h1.symm

/-- Pull-back along an open cover map does not raise the maximal order. -/
private theorem maxOrder_comap_le_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (I : X.IdealSheafData) :
    maxOrder (I.comap g) ≤ maxOrder I := by
  refine iSup₂_le fun y _ => ?_
  rw [multAt_comap_of_isOpenCoverMap hg]
  exact multAt_le_maxOrder I (g y)

/-- Pull-back along a surjective open cover map preserves the maximal order. -/
private theorem maxOrder_comap_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (hs : Surjective g) (I : X.IdealSheafData) :
    maxOrder (I.comap g) = maxOrder I := by
  refine le_antisymm (maxOrder_comap_le_of_isOpenCoverMap hg I) (iSup₂_le fun x _ => ?_)
  obtain ⟨y, rfl⟩ := hs.surj x
  rw [← multAt_comap_of_isOpenCoverMap hg]
  exact le_iSup₂ (f := fun y (_ : y ∈ Set.univ) => multAt (I.comap g) y) y trivial

/-- The local dimension is preserved by an open cover map. -/
private theorem topologicalKrullDimAt_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (y : X') :
    topologicalKrullDimAt X' y = topologicalKrullDimAt X (g y) := by
  obtain ⟨r, U, -, hU, hi⟩ := hg
  have hy : y ∈ ⨆ a, U a := hU ▸ trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  have e1 := (U a).ι.isOpenEmbedding.topologicalKrullDimAt_eq ⟨y, ha⟩
  have e2 := ((U a).ι ≫ g).isOpenEmbedding.topologicalKrullDimAt_eq ⟨y, ha⟩
  exact e1.trans e2.symm

/-- On an equidimensional scheme locally of finite type over a field, the local dimension at
every point is the dimension of any irreducible component. -/
private theorem topologicalKrullDimAt_eq_of_mem_irreducibleComponents' (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hX : TopologicalSpace.Equidimensional X) {C : Set X} (hC : C ∈ irreducibleComponents X)
    (x : X) : topologicalKrullDimAt X x = topologicalKrullDim C := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s x]
  refine le_antisymm (iSup₂_le fun D hD => (hX D hD.1 C hC).le) ?_
  exact (hX _ (irreducibleComponent_mem_irreducibleComponents x) C hC).symm.le.trans
    (le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ irreducibleComponents X ∧ x ∈ D}) =>
      topologicalKrullDim D) _ ⟨irreducibleComponent_mem_irreducibleComponents x,
        mem_irreducibleComponent⟩)

/-- The dimension of an irreducible component is the local dimension at its generic point. -/
private theorem topologicalKrullDim_eq_topologicalKrullDimAt (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) :
    ∃ η ∈ Z, topologicalKrullDimAt X η = topologicalKrullDim Z := by
  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  refine ⟨η, hη.mem, ?_⟩
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s η]
  refine le_antisymm (iSup₂_le fun Z' hZ' => ?_)
    (le_iSup₂ (f := fun Z' (_ : Z' ∈ {Z' | Z' ∈ irreducibleComponents X ∧ η ∈ Z'}) =>
      topologicalKrullDim Z') Z ⟨hZ, hη.mem⟩)
  have hle : Z ⊆ Z' := by
    rw [← (show closure {η} = Z from hη)]
    exact (isClosed_of_mem_irreducibleComponents Z' hZ'.1).closure_subset_iff.2
      (Set.singleton_subset_iff.2 hZ'.2)
  rw [(hZ.2 hZ'.1.1 hle).antisymm hle]

/-- Triples are stable under pull-back by open cover maps. -/
private theorem pullback_mem_triples_of_isOpenCoverMap (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) {Y : Scheme.{u}} (h : Y ⟶ t.X) (hh : IsOpenCoverMap h) :
    t.pullback h ∈ triples := by
  have : LocallyOfFiniteType t.sX := ht.2.2.1
  have : QuasiCompact t.sX := ht.2.2.2.1
  have : Smooth h := smooth_of_isOpenCoverMap hh
  have : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  have : CompactSpace t.X := (quasiCompact_iff_compactSpace t.sX).1 ‹_›
  have : IsNoetherian t.X := {}
  have : CompactSpace Y := by
    obtain ⟨r, U, -, hU, hi⟩ := hh
    refine ⟨?_⟩
    have : (Set.univ : Set Y) = ⋃ a, ((U a : Set Y)) := by
      rw [← TopologicalSpace.Opens.coe_iSup, hU]; rfl
    rw [this]
    refine isCompact_iUnion fun a => ?_
    have hc : IsCompact (Set.range ((U a).ι ≫ h)) :=
      NoetherianSpace.isCompact _
    have hemb := ((U a).ι ≫ h).isOpenEmbedding
    have : IsCompact (Set.univ : Set (U a)) := by
      rwa [hemb.isInducing.isCompact_iff, Set.image_univ]
    simpa using this.image (U a).ι.continuous
  have : QuasiCompact (h ≫ t.sX) := quasiCompact_of_compactSpace _
  refine mem_triples_iff.2 ⟨pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht) h, ?_⟩
  intro W hW W' hW'
  obtain ⟨η, -, hη⟩ := topologicalKrullDim_eq_topologicalKrullDimAt t.k (h ≫ t.sX) hW
  obtain ⟨η', -, hη'⟩ := topologicalKrullDim_eq_topologicalKrullDimAt t.k (h ≫ t.sX) hW'
  have hC := irreducibleComponent_mem_irreducibleComponents (h η)
  refine hη.symm.trans (Eq.trans ?_ hη')
  rw [topologicalKrullDimAt_of_isOpenCoverMap hh,
    topologicalKrullDimAt_of_isOpenCoverMap hh,
    topologicalKrullDimAt_eq_of_mem_irreducibleComponents' t.k t.sX ht.2.2.2.2.1 hC,
    topologicalKrullDimAt_eq_of_mem_irreducibleComponents' t.k t.sX ht.2.2.2.2.1 hC]

/-- A nonempty scheme with an open cover map to an equidimensional scheme of dimension `n`, of
finite type over a field, has dimension `n`. -/
private theorem hasDimensionIn_of_isOpenCoverMap {n : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (hd : HasDimensionIn t.X {n}) {Y : Scheme.{u}} [Nonempty Y]
    (h : Y ⟶ t.X) (hh : IsOpenCoverMap h) : HasDimensionIn Y {n} := by
  obtain ⟨n', rfl, hn'⟩ := hd
  refine ⟨n', rfl, ?_⟩
  have : LocallyOfFiniteType t.sX := ht.2.2.1
  have hcomp : ∀ C ∈ irreducibleComponents t.X,
      topologicalKrullDim C = ((n' : ℕ∞) : WithBot ℕ∞) := by
    intro C hC
    rw [← hn', topologicalKrullDim_eq_iSup_irreducibleComponents t.X]
    refine le_antisymm (le_iSup₂ (f := fun W (_ : W ∈ irreducibleComponents t.X) =>
      topologicalKrullDim W) C hC) (iSup₂_le fun W hW => (ht.2.2.2.2.1 W hW C hC).le)
  obtain ⟨x₀⟩ : Nonempty t.X := ⟨h (Classical.arbitrary Y)⟩
  have hC := irreducibleComponent_mem_irreducibleComponents x₀
  have hY : ∀ y : Y, topologicalKrullDimAt Y y = ((n' : ℕ∞) : WithBot ℕ∞) := fun y => by
    rw [topologicalKrullDimAt_of_isOpenCoverMap hh,
      topologicalKrullDimAt_eq_of_mem_irreducibleComponents' t.k t.sX ht.2.2.2.2.1 hC, hcomp _ hC]
  have : LocallyOfFiniteType (h ≫ t.sX) := by
    have : Smooth h := smooth_of_isOpenCoverMap hh
    infer_instance
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  refine le_antisymm ?_
    ((hY y₀).symm.le.trans (_root_.topologicalKrullDimAt_le_topologicalKrullDim y₀))
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents]
  refine iSup₂_le fun W hW => ?_
  obtain ⟨y, hyW⟩ := hW.1.nonempty
  rw [← hY y, topologicalKrullDimAt_eq_iSup_irreducibleComponents t.k Y (h ≫ t.sX) y]
  exact le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ irreducibleComponents Y ∧ y ∈ D}) =>
    topologicalKrullDim D) W ⟨hW, hyW⟩

/-- On an empty scheme every blow-up is empty, so pull-back with empty blow-ups deleted to an
empty scheme gives the empty sequence. -/
private theorem pullbackReduced_eq_nil_of_isEmpty {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y : Scheme.{u}} [IsEmpty Y] (h : Y ⟶ X), B.pullbackReduced h = .nil Y := by
  induction B with
  | nil X => intros; rfl
  | cons Z B ih =>
    intro Y _ h
    have hZ : Z.comap h = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      exact eq_bot_iff.2 fun y _ => isEmptyElim y
    simp only [ClosedBlowupSequence.pullbackReduced, hZ, dite_true]
    exact ih _

/-- A property local at the source holds for `f` if it holds on the nonempty members of a
family of open immersions covering the source. -/
private theorem of_forall_exists_isOpenImmersion (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] {X S : Scheme.{u}} (f : X ⟶ S) {N : ℕ} {V : Fin N → Scheme.{u}}
    (j : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (j i)] (hpt : ∀ x : X, ∃ i, ∃ v : V i, j i v = x)
    (h : ∀ i, Nonempty (V i) → P (j i ≫ f)) : P f := by
  choose i v hv using hpt
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun x => (j (i x)).opensRange)
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, ⟨v x, hv x⟩⟩) fun x => ?_
  have e : (j (i x)).opensRange.ι = (j (i x)).isoOpensRange.inv ≫ j (i x) := by
    rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e, Category.assoc]
  exact MorphismProperty.RespectsIso.precomp P _ _ (h _ ⟨v x⟩)

/-- On an affine open `U`, the zero scheme of `f ∈ J(U)` is contained in `J|_U`. -/
private theorem ker_spec_quotient_le_comap {X : Scheme.{u}} (U : X.affineOpens)
    (J : X.IdealSheafData) (f : Γ(X, U.1)) (hf : f ∈ J.ideal U) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫ U.2.isoSpec.inv).ker ≤
      J.comap U.1.ι := by
  have : IsAffine U.1.toScheme := U.2
  rw [Scheme.ker_of_isAffine]
  refine Scheme.IdealSheafData.le_of_isAffine ?_
  rw [Scheme.IdealSheafData.ofIdealTop_ideal, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have e := Scheme.IdealSheafData.map_ideal' J
    (U := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩) (V := U)
    (homOfLE (le_of_eq U.1.ι_image_top)).op
  rw [← e]
  intro a ha
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, homOfLE_refl, op_id] at ha ⊢
  rw [CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id] at ha
  change a ∈ Ideal.map _ (J.ideal U)
  rw [RingHom.mem_ker, Scheme.Hom.comp_appTop] at ha
  have key := IsAffineOpen.isoSpec_inv_appTop (X := X) (U := U.1) U.2
  have hz : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))).appTop
      ((Scheme.ΓSpecIso Γ(X, U.1)).inv (U.1.topIso.hom a)) = 0 := by
    rw [key, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp,
      RingHom.comp_apply] at ha
    exact ha
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
  have h2 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso Γ(X, U.1)).inv (U.1.topIso.hom a))) hnat
  rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [show (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (Ideal.span {f}))))).hom ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom (U.1.topIso.hom.hom a)) = 0
    from hz, map_zero] at h2
  have h3 : Ideal.Quotient.mk (Ideal.span {f}) (U.1.topIso.hom a) = 0 := by
    convert h2.symm using 2
    exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(X, U.1)) _).symm
  have hmem : U.1.topIso.hom a ∈ Ideal.span {f} := Ideal.Quotient.eq_zero_iff_mem.1 h3
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
  have ha' : a = U.1.topIso.inv (U.1.topIso.hom a) := (Iso.hom_inv_id_apply _ _).symm
  rw [ha', ← hr, map_mul]
  have hinv :
      U.1.topIso.inv.hom = (X.presheaf.map (homOfLE (le_of_eq U.1.ι_image_top)).op).hom := by
    rw [Scheme.Opens.topIso_inv]; congr 3
  have hfm : U.1.topIso.inv.hom f ∈
      Ideal.map (X.presheaf.map (homOfLE (le_of_eq U.1.ι_image_top)).op).hom (J.ideal U) := by
    rw [hinv]; exact Ideal.mem_map_of_mem _ hf
  exact Ideal.mul_mem_left _ _ hfm

/-- On an affine open `U`, the ideal of the zero scheme of `f ∈ Γ(U)` is generated by `f`. -/
private theorem ideal_ker_spec_quotient_top {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U.1)) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫
      U.2.isoSpec.inv).ker.ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {U.1.topIso.inv f} := by
  have : IsAffine U.1.toScheme := U.2
  rw [Scheme.ker_of_isAffine]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, Scheme.Hom.comp_appTop,
    IsAffineOpen.isoSpec_inv_appTop U.2]
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
  have hnat' : (Scheme.ΓSpecIso _).inv ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))).appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})) ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, hnat]
  rw [Category.assoc]; erw [hnat']
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  have h1 : U.1.topIso.hom.hom a = e a := rfl
  have h2 : f = e (U.1.topIso.inv.hom f) := (CommRingCat.hom_inv_apply U.1.topIso f).symm
  rw [h1]
  conv_lhs => rw [h2]
  rw [map_dvd_iff]

/-- On an affine open `U` of a scheme smooth over a field, the zero locus of a nonzerodivisor
`f ∈ Γ(U)` is of pure codimension one in `U`. -/
private theorem isPureCodimOne_support_ker_of_mem_nonZeroDivisors {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (U : X.affineOpens) (f : Γ(X, U.1))
    (hnzd : f ∈ nonZeroDivisors Γ(X, U.1)) :
    MMP.Mori.IsPureCodimOne (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫
      U.2.isoSpec.inv).ker.support := by
  set D := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫
      U.2.isoSpec.inv).ker
  have : LocallyOfFiniteType (U.1.ι ≫ sX) := inferInstance
  have : IsLocallyNoetherian U.1.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.1.ι ≫ sX)
  intro W hW
  set e := irreducibleSetEquivPoints (α := U.1.toScheme)
  have hWη : (W : Set U.1.toScheme) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set U.1.toScheme) := by rw [hWη]; exact subset_closure rfl
  have hηD : e W ∈ D.support := hW.1 hηW
  obtain ⟨z, hz⟩ : ∃ z, D.subschemeι z = e W := by
    rwa [← SetLike.mem_coe, ← D.range_subschemeι] at hηD
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1, ← hz]
  have hmax : IsMax z := by
    intro b hb
    rw [Scheme.le_iff_specializes] at hb ⊢
    have hcl := D.subschemeι.isClosedEmbedding
    have hb' : D.subschemeι b ⤳ e W := hz ▸ hb.map D.subschemeι.continuous
    have hbD : D.subschemeι b ∈ D.support := by
      rw [← SetLike.mem_coe, ← D.range_subschemeι]; exact ⟨b, rfl⟩
    have hle : W ≤ e.symm (D.subschemeι b) := by
      rwa [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes]
    have hsub : ((e.symm (D.subschemeι b) : TopologicalSpace.IrreducibleCloseds U.1.toScheme) :
        Set U.1.toScheme) ⊆ D.support := by
      change closure {D.subschemeι b} ⊆ _
      exact closure_minimal (Set.singleton_subset_iff.mpr hbD) D.support.isClosed
    have hge := hW.2 hsub hle
    rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes, ← hz] at hge
    exact hcl.isInducing.specializes_iff.mp hge
  have hz0 : ringKrullDim (D.subscheme.presheaf.stalk z) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr hmax]; rfl
  have hzD : D.subschemeι z ∈ D.support := hz ▸ hηD
  set η := D.subschemeι z
  let V : U.1.toScheme.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hηV : η ∈ (V : U.1.toScheme.Opens) := trivial
  set g := U.1.topIso.inv.hom f
  have hJ : D.ideal V = Ideal.span {g} := ideal_ker_spec_quotient_top U f
  have hg : g ∈ nonZeroDivisors Γ(U.1.toScheme, V.1) := by
    refine mem_nonZeroDivisors_iff_right.2 fun x hx => ?_
    have hφ : U.1.topIso.hom.hom g = f := CommRingCat.hom_inv_apply U.1.topIso f
    have h0 : U.1.topIso.hom.hom x * f = 0 := by rw [← hφ, ← map_mul, hx, map_zero]
    exact (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).1
      ((mem_nonZeroDivisors_iff_right.1 hnzd _ h0).trans (map_zero _).symm)
  have hst : IdealSheafData.stalk D η =
      Ideal.span {(U.1.toScheme.presheaf.germ V.1 η hηV).hom g} := by
    rw [IdealSheafData.stalk_eq_map_germ D η V hηV, hJ, Ideal.map_span, Set.image_singleton]
  let _ : Algebra Γ(U.1.toScheme, V.1) (U.1.toScheme.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk U.1.toScheme.presheaf ⟨η, hηV⟩
  have : IsLocalization.AtPrime (U.1.toScheme.presheaf.stalk η)
      (V.2.primeIdealOf ⟨η, hηV⟩).asIdeal := V.2.isLocalization_stalk ⟨η, hηV⟩
  have : Module.Flat Γ(U.1.toScheme, V.1) (U.1.toScheme.presheaf.stalk η) :=
    IsLocalization.flat _ (V.2.primeIdealOf ⟨η, hηV⟩).asIdeal.primeCompl
  have hgreg : IsSMulRegular (U.1.toScheme.presheaf.stalk η)
      ((U.1.toScheme.presheaf.germ V.1 η hηV).hom g) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (R := Γ(U.1.toScheme, V.1))
      (M := U.1.toScheme.presheaf.stalk η) hg
  have hgm : (U.1.toScheme.presheaf.germ V.1 η hηV).hom g ∈
      IsLocalRing.maximalIdeal (U.1.toScheme.presheaf.stalk η) := by
    have hmem := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := D) (U := V) hηV).mp hzD
    rw [Scheme.mem_zeroLocus_iff] at hmem
    have hnot := hmem g (by rw [SetLike.mem_coe, hJ]; exact Ideal.mem_span_singleton_self g)
    rwa [Scheme.mem_basicOpen _ _ _ hηV] at hnot
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hgreg hgm
  rw [← hst, ringKrullDim_eq_of_ringEquiv (MMP.Flips.ResolutionInputs.stalkQuotientEquiv D z),
    hz0, zero_add, ringKrullDim_stalk_eq_coheight] at hdim
  exact_mod_cast hdim.symm

/-- On an affine open `U` of a scheme smooth over `k`, the zero scheme of a nonzerodivisor
`f ∈ J(U)` whose zero scheme `Spec(Γ(U)/(f))` is smooth over `k` is a smooth hypersurface of `U`
contained in `J|_U`. -/
private theorem exists_isSmoothHypersurface_of_section {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (U : X.affineOpens) (J : X.IdealSheafData)
    (f : Γ(X, U.1)) (hf : f ∈ J.ideal U) (hnzd : f ∈ nonZeroDivisors Γ(X, U.1))
    (hs : Smooth (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫
      U.2.isoSpec.inv ≫ U.1.ι ≫ sX)) :
    ∃ H : U.1.toScheme.IdealSheafData, IsSmoothHypersurface (U.1.ι ≫ sX) H ∧
      H ≤ J.comap U.1.ι := by
  set i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫ U.2.isoSpec.inv
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion i := by dsimp [i]; infer_instance
  refine ⟨i.ker, ⟨?_, isPureCodimOne_support_ker_of_mem_nonZeroDivisors sX U f hnzd⟩, ?_⟩
  · have he : i.ker.subschemeι ≫ U.1.ι ≫ sX = inv i.toImage ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫
          U.2.isoSpec.inv ≫ U.1.ι ≫ sX := by
      have hι : i.imageι = inv i.toImage ≫ i :=
        (IsIso.eq_inv_comp _).2 (Scheme.Hom.toImage_imageι i)
      change i.imageι ≫ _ = _
      rw [hι]
      simp only [Category.assoc, i]
    rw [he]
    have hinv : Smooth (inv i.toImage) := inferInstance
    exact MMP.Mori.isSmoothScheme_of_smooth (MorphismProperty.comp_mem @Smooth _ _ hinv hs)
  · exact ker_spec_quotient_le_comap U J f hf

/-! ### Local triples on a surjective open cover map -/

section LocalCover

open Limits Topology

/-- Distinct summands of a coproduct of schemes are disjoint. -/
private theorem sigmaι_apply_ne {N : ℕ} (V : Fin N → Scheme.{u}) {i j : Fin N} (h : i ≠ j)
    (a : V i) (b : V j) : Sigma.ι V i a ≠ Sigma.ι V j b := by
  intro e
  have hx : Sigma.ι V i a ∈ (Sigma.ι V i).opensRange ⊓ (Sigma.ι V j).opensRange :=
    ⟨⟨a, rfl⟩, ⟨b, e.symm⟩⟩
  rwa [(disjoint_opensRange_sigmaι V i j h).eq_bot] at hx

/-- Every point of a coproduct of schemes lies in a summand. -/
private theorem exists_sigmaι_apply_eq {N : ℕ} (V : Fin N → Scheme.{u}) (y : ↥(∐ V : Scheme.{u})) :
    ∃ i, ∃ v : V i, Sigma.ι V i v = y := by
  obtain ⟨⟨i⟩, v, hv⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (Discrete.functor V) y
  exact ⟨i, v, hv⟩

/-- A summand of a finite coproduct of schemes is closed: the image of a closed subset of a
summand is closed. -/
private theorem isClosed_image_sigmaι {N : ℕ} (V : Fin N → Scheme.{u}) (i : Fin N)
    {Z : Set (V i)} (hZ : IsClosed Z) : IsClosed (Sigma.ι V i '' Z) := by
  rw [← isOpen_compl_iff]
  have e : (Sigma.ι V i '' Z)ᶜ =
      (Sigma.ι V i '' Zᶜ) ∪ ⋃ (j : Fin N) (_ : j ≠ i), Set.range (Sigma.ι V j) := by
    ext y
    obtain ⟨j, v, rfl⟩ := exists_sigmaι_apply_eq V y
    constructor
    · intro hy
      by_cases hji : j = i
      · subst hji
        exact Or.inl ⟨v, fun hv => hy ⟨v, hv, rfl⟩, rfl⟩
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, v, rfl⟩)
    · rintro (⟨w, hw, hwv⟩ | hy) ⟨z, hz, hzv⟩
      · exact hw ((Sigma.ι V i).isOpenEmbedding.injective (hzv.trans hwv.symm) ▸ hz)
      · obtain ⟨j', hj', w, hw⟩ := Set.mem_iUnion₂.1 hy
        exact sigmaι_apply_ne V (Ne.symm hj') z w (hzv.trans hw.symm)
  rw [e]
  exact ((Sigma.ι V i).isOpenEmbedding.isOpenMap _ hZ.isOpen_compl).union
    (isOpen_iUnion fun j => isOpen_iUnion fun _ => (Sigma.ι V j).isOpenEmbedding.isOpen_range)

/-- The map from a finite coproduct of schemes induced by open immersions is an open cover
map. -/
private theorem isOpenCoverMap_sigmaDesc {N : ℕ} (V : Fin N → Scheme.{u}) {X : Scheme.{u}}
    (j : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (j i)] : IsOpenCoverMap (Sigma.desc j) := by
  refine isOpenCoverMap_of_finite (fun i => (Sigma.ι V i).opensRange)
    (fun a b hab => disjoint_opensRange_sigmaι V a b hab) ?_ fun i => ?_
  · refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨i, v, rfl⟩ := exists_sigmaι_apply_eq V y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, v, rfl⟩
  · have e : (Sigma.ι V i).opensRange.ι = (Sigma.ι V i).isoOpensRange.inv ≫ Sigma.ι V i := by
      rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
    rw [e, Category.assoc, Sigma.ι_desc]
    infer_instance

/-- An inequality of ideal sheaves on a finite coproduct holds as soon as it holds on every
summand. -/
private theorem le_of_forall_comap_sigmaι_le {N : ℕ} (V : Fin N → Scheme.{u})
    {A B : (∐ V).IdealSheafData}
    (h : ∀ i, A.comap (Sigma.ι V i) ≤ B.comap (Sigma.ι V i)) : A ≤ B := by
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (ι := Σ i, (V i).affineOpens)
    (fun p => ⟨Sigma.ι V p.1 ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion _⟩) ?_ fun p => ?_
  · rw [eq_top_iff]
    intro y _
    obtain ⟨i, v, rfl⟩ := exists_sigmaι_apply_eq V y
    have hv : v ∈ (⨆ W : (V i).affineOpens, (W : (V i).Opens)) := by
      rw [iSup_affineOpens_eq_top (V i)]; trivial
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 hv
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, W⟩, ⟨v, hW, rfl⟩⟩
  · have hp := h p.1 p.2
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hp
    intro a ha
    have key : ((Sigma.ι V p.1).appIso p.2.1).inv.hom
        (((Sigma.ι V p.1).appIso p.2.1).hom.hom a) = a :=
      Iso.hom_inv_id_apply ((Sigma.ι V p.1).appIso p.2.1) a
    have := hp (show ((Sigma.ι V p.1).appIso p.2.1).hom.hom a ∈ Ideal.comap _ _ from by
      rwa [Ideal.mem_comap, key])
    rwa [Ideal.mem_comap, key] at this

/-- A scheme smooth over a field is reduced. -/
private theorem isReduced_of_isSmoothScheme {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (hs : MMP.Mori.IsSmoothScheme s) : IsReduced X := by
  have : Smooth s := MMP.Mori.IsSmoothScheme.smooth hs
  have : ∀ z : X, _root_.IsReduced (X.presheaf.stalk z) := fun z => by
    have := AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth_over_field s z
    have := IsRegularLocalRing.isDomain (X.presheaf.stalk z)
    infer_instance
  exact isReduced_of_isReduced_stalk _

section Topology

variable {A T : Type*} [TopologicalSpace A] [TopologicalSpace T] {ψ : A → T}

/-- The closure of the image of an irreducible closed subset under an open embedding. -/
private def closureImage (hψ : IsOpenEmbedding ψ) (Z : IrreducibleCloseds A) :
    IrreducibleCloseds T :=
  ⟨closure (ψ '' Z), (Z.isIrreducible.image ψ hψ.continuous.continuousOn).closure,
    isClosed_closure⟩

/-- The preimage of an irreducible closed subset meeting the image of an open embedding. -/
private def preimageIrr (hψ : IsOpenEmbedding ψ) (B : IrreducibleCloseds T)
    (hne : ((B : Set T) ∩ Set.range ψ).Nonempty) : IrreducibleCloseds A :=
  ⟨ψ ⁻¹' B, B.isIrreducible.preimage hψ hne, B.isClosed.preimage hψ.continuous⟩

/-- `closureImage` is a section of the preimage. -/
private lemma preimage_closureImage (hψ : IsOpenEmbedding ψ) (Z : IrreducibleCloseds A) :
    ψ ⁻¹' (closureImage hψ Z : Set T) = Z := by
  change ψ ⁻¹' closure (ψ '' Z) = Z
  rw [← hψ.isInducing.closure_eq_preimage_closure_image, Z.isClosed.closure_eq]

/-- `closureImage` undoes `preimageIrr`. -/
private lemma closureImage_preimageIrr (hψ : IsOpenEmbedding ψ) (B : IrreducibleCloseds T)
    (hne : ((B : Set T) ∩ Set.range ψ).Nonempty) :
    closureImage hψ (preimageIrr hψ B hne) = B := by
  have hne' : (ψ ⁻¹' B).Nonempty := by obtain ⟨_, hb, x, rfl⟩ := hne; exact ⟨x, hb⟩
  exact SetLike.coe_injective <| closure_image_preimage_of_isPreirreducible ψ hψ.isOpenMap B
    hne' B.isIrreducible.isPreirreducible B.isClosed

/-- Taking closures of images along an open embedding preserves codimension. -/
private lemma codimension_closureImage (hψ : IsOpenEmbedding ψ) (Z : IrreducibleCloseds A) :
    codimension (closureImage hψ Z) = codimension Z := by
  rw [codimension_eq_coheight, codimension_eq_coheight]
  have hmono : StrictMono (closureImage hψ) := fun a b hab ↦
    lt_of_le_of_ne (closure_mono (Set.image_mono hab.le)) fun h ↦ hab.ne <|
      SetLike.coe_injective <| by
        simpa only [preimage_closureImage] using
          congrArg (fun W : IrreducibleCloseds T ↦ ψ ⁻¹' (W : Set T)) h
  refine (Order.coheight_eq_of_strictMono _ hmono (fun a B hab ↦ ?_) Z).symm
  have hne : ((B : Set T) ∩ Set.range ψ).Nonempty := by
    obtain ⟨x, hx⟩ := a.isIrreducible.nonempty
    exact ⟨ψ x, hab.le (subset_closure ⟨x, hx, rfl⟩), x, rfl⟩
  refine ⟨preimageIrr hψ B hne, lt_of_le_of_ne (fun x hx ↦ hab.le (subset_closure ⟨x, hx, rfl⟩))
    ?_, closureImage_preimageIrr hψ B hne⟩
  rintro rfl
  exact hab.ne (closureImage_preimageIrr hψ B hne)

end Topology

set_option backward.isDefEq.respectTransparency false in
/-- Smooth hypersurfaces on the summands of a finite coproduct, each contained in the restriction
of an ideal sheaf `J`, glue to a smooth hypersurface contained in `J`: the reduced structure on
the union of their images. -/
private theorem exists_isSmoothHypersurface_sigma {k : Type u} [Field k] [CharZero k] {N : ℕ}
    (V : Fin N → Scheme.{u}) (s : (∐ V) ⟶ Spec (.of k)) (J : (∐ V).IdealSheafData)
    (H : ∀ i, (V i).IdealSheafData) (hH : ∀ i, IsSmoothHypersurface (Sigma.ι V i ≫ s) (H i))
    (hle : ∀ i, H i ≤ J.comap (Sigma.ι V i)) :
    ∃ H' : (∐ V).IdealSheafData, IsSmoothHypersurface s H' ∧ H' ≤ J := by
  classical
  have hred : ∀ i, IsReduced (H i).subscheme := fun i =>
    isReduced_of_isSmoothScheme _ (hH i).1
  let C : Closeds ↥(∐ V : Scheme.{u}) :=
    ⟨⋃ i, Sigma.ι V i '' ((H i).support : Set (V i)),
      isClosed_iUnion_of_finite fun i => isClosed_image_sigmaι V i (H i).support.isClosed⟩
  have hCcoe : (C : Set ↥(∐ V : Scheme.{u})) = ⋃ i, Sigma.ι V i '' ((H i).support : Set (V i)) :=
    rfl
  have hC : ∀ i, Sigma.ι V i ⁻¹' (C : Set ↥(∐ V : Scheme.{u})) = ((H i).support : Set (V i)) := by
    intro i
    ext z
    rw [hCcoe, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨j, w, hw, hwz⟩
      by_cases hji : j = i
      · subst hji
        rwa [← (Sigma.ι V j).isOpenEmbedding.injective hwz]
      · exact absurd hwz (sigmaι_apply_ne V hji w z)
    · intro hz
      exact ⟨i, z, hz, rfl⟩
  let H' := Scheme.IdealSheafData.vanishingIdeal C
  have hsupp : (H'.support : Set ↥(∐ V : Scheme.{u})) = C :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal C
  have hcomap : ∀ i, H'.comap (Sigma.ι V i) = H i := fun i => by
    have : IsReduced H'.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal C
    have : IsReduced (H'.comap (Sigma.ι V i)).subscheme :=
      isReduced_of_isOpenImmersion
        ((H'.comapIso (Sigma.ι V i)).hom ≫ Limits.pullback.snd (Sigma.ι V i) H'.subschemeι)
    have := hred i
    rw [← MMP.Mori.vanishingIdeal_support_eq_self (H'.comap (Sigma.ι V i)),
      ← MMP.Mori.vanishingIdeal_support_eq_self (H i)]
    congr 1
    apply SetLike.coe_injective
    rw [Scheme.IdealSheafData.support_comap]
    change Sigma.ι V i ⁻¹' (H'.support : Set ↥(∐ V : Scheme.{u})) = _
    rw [hsupp, hC]
  refine ⟨H', ⟨?_, ?_⟩, le_of_forall_comap_sigmaι_le V fun i => (hcomap i).symm ▸ hle i⟩
  · -- smoothness is local on the summands
    let j : ∀ i, (H'.comap (Sigma.ι V i)).subscheme ⟶ H'.subscheme := fun i =>
      (H'.comapIso (Sigma.ι V i)).hom ≫ Limits.pullback.snd (Sigma.ι V i) H'.subschemeι
    have hsm : Smooth (H'.subschemeι ≫ s) := by
      refine of_forall_exists_isOpenImmersion @Smooth _ j (fun z => ?_) fun i _ => ?_
      · obtain ⟨i, v, hv⟩ := exists_sigmaι_apply_eq V (H'.subschemeι z)
        obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback v z hv
        refine ⟨i, (H'.comapIso (Sigma.ι V i)).inv w, ?_⟩
        simp only [j, Scheme.Hom.comp_apply]
        rwa [← Scheme.Hom.comp_apply (H'.comapIso (Sigma.ι V i)).inv, Iso.inv_hom_id]
      · have he : j i ≫ H'.subschemeι ≫ s =
            (H'.comap (Sigma.ι V i)).subschemeι ≫ Sigma.ι V i ≫ s := by
          simp only [j, Category.assoc]
          rw [← Limits.pullback.condition_assoc, ← H'.comapIso_hom_fst (Sigma.ι V i),
            Category.assoc]
        rw [he]
        have := (hH i).1
        rw [← hcomap i] at this
        exact MMP.Mori.IsSmoothScheme.smooth this
    exact MMP.Mori.isSmoothScheme_of_smooth hsm
  · -- pure codimension one is local on the summands
    intro W hW
    have hWsub :
        (W : Set ↥(∐ V : Scheme.{u})) ⊆ ⋃ i, Sigma.ι V i '' ((H i).support : Set (V i)) := by
      rw [← hCcoe, ← hsupp]; exact hW.1
    obtain ⟨i, hi⟩ :
        ∃ i, (W : Set ↥(∐ V : Scheme.{u})) ⊆ Sigma.ι V i '' ((H i).support : Set (V i)) := by
      obtain ⟨z, hz, hWz⟩ := (isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible)
        (Finset.univ.image fun i => Sigma.ι V i '' ((H i).support : Set (V i)))
        (by
          intro z hz
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
          exact isClosed_image_sigmaι V i (H i).support.isClosed)
        (by
          intro x hx
          obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hWsub hx)
          exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)), hxi⟩)
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨i, hWz⟩
    have hψ := (Sigma.ι V i).isOpenEmbedding
    have hne : ((W : Set ↥(∐ V : Scheme.{u})) ∩ Set.range (Sigma.ι V i)).Nonempty := by
      obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
      obtain ⟨v, -, rfl⟩ := hi hx
      exact ⟨_, hx, v, rfl⟩
    let W' := preimageIrr hψ W hne
    have hWW' : closureImage hψ W' = W := closureImage_preimageIrr hψ W hne
    have hW'Z : (W' : Set (V i)) ⊆ ((H i).support : Set (V i)) := by
      intro v hv
      obtain ⟨v', hv', e⟩ := hi hv
      rwa [← hψ.injective e]
    have hmax :
        Maximal (fun B : IrreducibleCloseds (V i) => (B : Set (V i)) ⊆ (H i).support) W' := by
      refine ⟨hW'Z, fun B hB hle => ?_⟩
      have hBC : (closureImage hψ B : Set ↥(∐ V : Scheme.{u})) ⊆ H'.support := by
        rw [hsupp, hCcoe]
        refine (closure_minimal (Set.image_mono hB)
          (isClosed_image_sigmaι V i (H i).support.isClosed)).trans ?_
        exact Set.subset_iUnion (fun i => Sigma.ι V i '' ((H i).support : Set (V i))) i
      have hle' : W ≤ closureImage hψ B := by
        rw [← hWW']; exact closure_mono (Set.image_mono hle)
      have := hW.2 hBC hle'
      intro v hv
      exact this (subset_closure ⟨v, hv, rfl⟩)
    rw [← hWW', codimension_closureImage hψ W']
    exact (hH i).2 W' hmax

end LocalCover

/-- Restricting a nonzerodivisor `g` of an affine open `V` to a basic open `D(a) ⊆ V` keeps it a
nonzerodivisor, and keeps its zero scheme smooth over the base. -/
private theorem restrict_basicOpen {X : Scheme.{u}} {S : Scheme.{u}} (sX : X ⟶ S)
    {V : X.Opens} (hV : IsAffineOpen V) (a g : Γ(X, V)) (hg : g ∈ nonZeroDivisors Γ(X, V))
    (hs : Smooth (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {g}))) ≫
        hV.isoSpec.inv ≫ V.ι ≫ sX)) :
    X.presheaf.map (homOfLE (X.basicOpen_le a)).op g ∈ nonZeroDivisors Γ(X, X.basicOpen a) ∧
      Smooth (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {X.presheaf.map (homOfLE (X.basicOpen_le a)).op g}))) ≫
        (hV.basicOpen a).isoSpec.inv ≫ (X.basicOpen a).ι ≫ sX) := by
  let ρ := X.presheaf.map (homOfLE (X.basicOpen_le a)).op
  letI : Algebra Γ(X, V) Γ(X, X.basicOpen a) := ρ.hom.toAlgebra
  have : IsLocalization.Away a Γ(X, X.basicOpen a) := hV.isLocalization_basicOpen a
  refine ⟨IsLocalization.map_nonZeroDivisors_le (Submonoid.powers a) _ ⟨g, hg, rfl⟩, ?_⟩
  set I : Ideal Γ(X, V) := Ideal.span {g}
  set B := Γ(X, X.basicOpen a) ⧸ I.map (algebraMap Γ(X, V) Γ(X, X.basicOpen a))
  have hJ : Ideal.span {ρ g} = I.map (algebraMap Γ(X, V) Γ(X, X.basicOpen a)) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  rw [hJ]
  have : IsLocalization.Away (Ideal.Quotient.mk I a) B := by
    have := IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
      (Submonoid.powers a) Γ(X, X.basicOpen a) I
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at this
  have hsq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (I.map (algebraMap Γ(X, V) Γ(X, X.basicOpen a))))) ≫
        (hV.basicOpen a).isoSpec.inv ≫ (X.basicOpen a).ι =
      Spec.map (CommRingCat.ofHom (algebraMap (Γ(X, V) ⧸ I) B)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.isoSpec.inv ≫ V.ι := by
    rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.isoSpec_inv_ι,
      ← hV.map_fromSpec (hV.basicOpen a) (homOfLE (X.basicOpen_le a)).op,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
  have h := hsq =≫ sX
  simp only [Category.assoc] at h
  rw [h]
  have := IsOpenImmersion.of_isLocalization (S := B) (Ideal.Quotient.mk I a)
  infer_instance

/-- A section is a unit on every open inside its basic open. -/
private theorem isUnit_map_of_le_basicOpen {X : Scheme.{u}} {U W : X.Opens} (h : Γ(X, U))
    (i : W ≤ U) (hW : W ≤ X.basicOpen h) : IsUnit (X.presheaf.map (homOfLE i).op h) := by
  apply RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace
  intro y hy
  convert (X.mem_basicOpen h y (i hy)).1 (hW hy) using 1
  exact X.presheaf.germ_res_apply (homOfLE i) y hy h

/-- The zero scheme of a unit is empty, hence smooth over anything. -/
private theorem smooth_of_isUnit {R : CommRingCat.{u}} {Y : Scheme.{u}} {f : R} (hf : IsUnit f)
    (φ : Spec (CommRingCat.of R) ⟶ Y) :
    Smooth (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫ φ) := by
  have : Subsingleton (R ⧸ Ideal.span {f}) :=
    Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 hf)
  have : IsEmpty (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum _))
  infer_instance

/-- If the stalk of `J` at `x` is not contained in an ideal `P` of the local ring, some section
of `J` over an affine neighbourhood of `x` has germ outside `P`. -/
private theorem exists_mem_ideal_germ_notMem {X : Scheme.{u}} (J : X.IdealSheafData) {x : X}
    {U₀ : X.Opens} (hU₀ : IsAffineOpen U₀) (hx : x ∈ U₀) {P : Ideal (X.presheaf.stalk x)}
    (h : ¬ IdealSheafData.stalk J x ≤ P) :
    ∃ g ∈ J.ideal ⟨U₀, hU₀⟩, X.presheaf.germ U₀ x hx g ∉ P := by
  rwa [IdealSheafData.stalk_eq_map_germ J x ⟨U₀, hU₀⟩ hx, Ideal.map_le_iff_le_comap,
    SetLike.not_le_iff_exists] at h

/-! ### Push-forwards of blow-up sequences -/

section Pushforward

open Limits

/-- The image of a closed subscheme is the kernel of the composite. -/
private theorem map_eq_ker {S X : Scheme.{u}} (j : S ⟶ X) (Z : S.IdealSheafData) :
    Z.map j = (Z.subschemeι ≫ j).ker := by
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι]

/-- The image of a closed subscheme under a closed immersion commutes with base change. -/
private theorem comap_map_of_isPullback {X X' Y Y' : Scheme.{u}} {j : Y ⟶ X} {g : X' ⟶ X}
    {gY : Y' ⟶ Y} {j' : Y' ⟶ X'} [IsClosedImmersion j] (sq : IsPullback gY j' j g)
    (Z : Y.IdealSheafData) : (Z.map j).comap g = (Z.comap gY).map j' := by
  have sq' := (Kollar.isPullback_comapSubschemeProj gY Z).paste_horiz sq.flip
  rw [map_eq_ker, map_eq_ker]
  exact (Kollar.ker_eq_comap_of_isPullback sq').symm

/-- Two morphisms `B_W Y → B_Z X` over `f : Y → X`, `W = f⁻¹Z`, are equal. -/
private theorem eq_of_comp_blowUpToBase {X Y : Scheme.{u}} (f : Y ⟶ X) (Z : X.IdealSheafData)
    {W : Y.IdealSheafData} (hW : Z.comap f = W) (c₁ c₂ : blowUp W ⟶ blowUp Z)
    (h₁ : c₁ ≫ blowUpToBase Z = blowUpToBase W ≫ f)
    (h₂ : c₂ ≫ blowUpToBase Z = blowUpToBase W ≫ f) : c₁ = c₂ := by
  subst hW
  have hc := isCartierOver_blowUpToBase_comp f Z
  exact (blowUpLift_unique _ _ hc _ h₁).trans (blowUpLift_unique _ _ hc _ h₂).symm

/-- Transport along an equality of centres commutes with the blow-up map. -/
private theorem eqToHom_blowUpToBase {Y : Scheme.{u}} {W W' : Y.IdealSheafData} (e : W = W') :
    eqToHom (congrArg blowUp e) ≫ blowUpToBase W' = blowUpToBase W := by
  subst e; simp

/-- Canonical lifts along a cartesian square with a flat side form a cartesian square. -/
private theorem isPullback_canonicalLift {X X' Y Y' : Scheme.{u}} {j : Y ⟶ X} {g : X' ⟶ X}
    {gY : Y' ⟶ Y} {j' : Y' ⟶ X'} [Flat g] (sq : IsPullback gY j' j g) (Z : X.IdealSheafData)
    (e : (Z.comap g).comap j' = (Z.comap j).comap gY) :
    IsPullback (canonicalLift gY (Z.comap j))
      (eqToHom (congrArg blowUp e.symm) ≫ canonicalLift j' (Z.comap g))
      (canonicalLift j Z) (canonicalLift g Z) := by
  have : Flat gY := MorphismProperty.of_isPullback (P := @Flat) sq.flip ‹_›
  have S1 := (Kollar.isPullback_canonicalLift_of_flat gY (Z.comap j)).flip
  have Bsq := (Kollar.isPullback_canonicalLift_of_flat g Z).flip
  have h1 : (eqToHom (congrArg blowUp e.symm) ≫ canonicalLift j' (Z.comap g)) ≫
      blowUpToBase (Z.comap g) = blowUpToBase ((Z.comap j).comap gY) ≫ j' := by
    rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
      eqToHom_blowUpToBase e.symm]
  refine IsPullback.of_bot ?_ ?_ Bsq
  · rw [h1, canonicalLift_comp_blowUpToBase]
    exact S1.paste_vert sq
  · refine eq_of_comp_blowUpToBase (gY ≫ j) Z
      (by rw [Scheme.IdealSheafData.comap_comp]) _ _ ?_ ?_
    · rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
        canonicalLift_comp_blowUpToBase, Category.assoc]
    · rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc, h1,
        Category.assoc, sq.w]

/-- **Push-forwards descend along flat surjections.** -/
private theorem isPushforward_of_pullback : ∀ {Y : Scheme.{u}} (BS : ClosedBlowupSequence Y)
    {X X' Y' : Scheme.{u}} {j : Y ⟶ X} {g : X' ⟶ X} {gY : Y' ⟶ Y} {j' : Y' ⟶ X'}
    [IsClosedImmersion j] [Flat g] [Surjective g] (BX : ClosedBlowupSequence X),
    IsPullback gY j' j g →
    ClosedBlowupSequence.IsPushforward j' (BS.pullback gY) (BX.pullback g) →
    ClosedBlowupSequence.IsPushforward j BS BX := by
  intro Y BS
  induction BS with
  | nil Y =>
    intro X X' Y' j g gY j' _ _ _ BX sq hP
    cases BX with
    | nil => trivial
    | cons Z BX => exact hP.elim
  | cons ZS BS ih =>
    intro X X' Y' j g gY j' _ _ _ BX sq hP
    cases BX with
    | nil => exact hP.elim
    | cons Z BX =>
      have : Flat gY := MorphismProperty.of_isPullback (P := @Flat) sq.flip ‹_›
      have : Surjective gY := MorphismProperty.of_isPullback (P := @Surjective) sq.flip ‹_›
      obtain ⟨h, hm, hP⟩ := hP
      have hZS : Z.comap j = ZS := by
        refine Kollar.eq_of_comap_eq_of_flat_of_surjective gY ?_
        rw [← Scheme.IdealSheafData.comap_comp, sq.w, Scheme.IdealSheafData.comap_comp, h]
      subst hZS
      refine ⟨rfl, ?_, ?_⟩
      · refine Kollar.eq_of_comap_eq_of_flat_of_surjective g ?_
        rwa [comap_map_of_isPullback sq]
      · rw [eqToHom_refl, Category.id_comp]
        have := Kollar.surjective_canonicalLift g Z
        have := Kollar.flat_canonicalLift g Z
        have := Bridges.isClosedImmersion_canonicalLift j Z
        exact ih BX (isPullback_canonicalLift sq Z h) hP

/-- Push-forwards compose. -/
private theorem isPushforward_comp : ∀ {S : Scheme.{u}} (B₀ : ClosedBlowupSequence S)
    {Y X : Scheme.{u}} (j₁ : S ⟶ Y) (j₂ : Y ⟶ X) (B₁ : ClosedBlowupSequence Y)
    (B₂ : ClosedBlowupSequence X),
    ClosedBlowupSequence.IsPushforward j₁ B₀ B₁ → ClosedBlowupSequence.IsPushforward j₂ B₁ B₂ →
    ClosedBlowupSequence.IsPushforward (j₁ ≫ j₂) B₀ B₂ := by
  intro S B₀
  induction B₀ with
  | nil S =>
    intro Y X j₁ j₂ B₁ B₂ h₁ h₂
    cases B₁ with
    | cons _ _ => exact h₁.elim
    | nil =>
      cases B₂ with
      | nil => trivial
      | cons _ _ => exact h₂.elim
  | cons Z₀ B₀ ih =>
    intro Y X j₁ j₂ B₁ B₂ h₁ h₂
    cases B₁ with
    | nil => exact h₁.elim
    | cons Z₁ B₁ =>
      cases B₂ with
      | nil => exact h₂.elim
      | cons Z₂ B₂ =>
        obtain ⟨e₂, m₂, P₂⟩ := h₂
        subst e₂
        obtain ⟨e₁, m₁, P₁⟩ := h₁
        subst e₁
        rw [eqToHom_refl, Category.id_comp] at P₁ P₂
        have hc : Z₂.comap (j₁ ≫ j₂) = (Z₂.comap j₂).comap j₁ :=
          Scheme.IdealSheafData.comap_comp _ _ _
        refine ⟨hc, ?_, ?_⟩
        · rw [Scheme.IdealSheafData.map_comp, ← m₁, ← m₂]
        · have he : eqToHom (congrArg blowUp hc.symm) ≫ canonicalLift (j₁ ≫ j₂) Z₂ =
              canonicalLift j₁ (Z₂.comap j₂) ≫ canonicalLift j₂ Z₂ := by
            refine eq_of_comp_blowUpToBase (j₁ ≫ j₂) Z₂ hc _ _ ?_ ?_
            · rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
                eqToHom_blowUpToBase hc.symm]
            · rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
                canonicalLift_comp_blowUpToBase, Category.assoc]
          rw [he]
          exact ih _ _ _ _ P₁ P₂

/-- Every blow-up sequence has a push-forward along a closed immersion. -/
private theorem exists_isPushforward : ∀ {S : Scheme.{u}} (B : ClosedBlowupSequence S)
    {X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j],
    ∃ B' : ClosedBlowupSequence X, ClosedBlowupSequence.IsPushforward j B B' := by
  intro S B
  induction B with
  | nil S => intro X j _; exact ⟨.nil X, trivial⟩
  | cons Z B ih =>
    intro X j _
    have h : (Z.map j).comap j = Z := Z.comap_map_of_isClosedImmersion j
    have := Bridges.isClosedImmersion_canonicalLift j (Z.map j)
    obtain ⟨B', hB'⟩ := ih (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift j (Z.map j))
    exact ⟨.cons (Z.map j) B', h, rfl, hB'⟩

/-- `ClosedBlowupSequence.pushforward` is a push-forward. -/
private theorem isPushforward_pushforward {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (B : ClosedBlowupSequence S) : ClosedBlowupSequence.IsPushforward j B (B.pushforward j) := by
  have hex := exists_isPushforward B j
  rw [ClosedBlowupSequence.pushforward, dif_pos hex]
  exact hex.choose_spec

end Pushforward

/-! ### Open and closed subschemes -/

section OpenClosed

open Limits

/-- A point whose image lies in the range of `f` lies in the range of the base change of `f`. -/
private theorem mem_range_of_isPullback {P A B C : Scheme.{u}} {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (sq : IsPullback fst snd f g) {b : B} (hb : g b ∈ Set.range f) :
    b ∈ Set.range snd := by
  obtain ⟨a, ha⟩ := hb
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback a b ha
  refine ⟨sq.isoPullback.inv z, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz]

/-- An inclusion of ideal sheaves can be checked on two open immersions covering the scheme. -/
private theorem le_of_comap_le_of_cover {X Y W : Scheme.{u}} (j : Y ⟶ X) (w : W ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion w] (hcov : ∀ x, x ∈ Set.range j ∨ x ∈ Set.range w)
    {I J : X.IdealSheafData} (hj : I.comap j ≤ J.comap j) (hw : I.comap w ≤ J.comap w) :
    I ≤ J := by
  have key : ∀ {V : Scheme.{u}} (h : V ⟶ X) [IsOpenImmersion h], I.comap h ≤ J.comap h →
      ∀ v : V, IdealSheafData.stalk I (h v) ≤ IdealSheafData.stalk J (h v) := by
    intro V h _ hle v
    have hv : IdealSheafData.stalk (I.comap h) v ≤ IdealSheafData.stalk (J.comap h) v :=
      iSup₂_mono fun U _ => Ideal.map_mono (hle U)
    rw [IdealSheafData.stalk_comap, IdealSheafData.stalk_comap] at hv
    have hb := ConcreteCategory.bijective_of_isIso (h.stalkMap v)
    have := Ideal.comap_mono (f := (h.stalkMap v).hom) hv
    rwa [Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb] at this
  refine IdealSheafData.le_of_stalk_le I J fun x => ?_
  rcases hcov x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · exact key j hj y
  · exact key w hw z

/-- An ideal sheaf whose inverse images along two open immersions covering the scheme are the
unit ideal is the unit ideal. -/
private theorem eq_top_of_comap_eq_top {X Y W : Scheme.{u}} (j : Y ⟶ X) (w : W ⟶ X)
    (hcov : ∀ x, x ∈ Set.range j ∨ x ∈ Set.range w) {Z : X.IdealSheafData}
    (hj : Z.comap j = ⊤) (hw : Z.comap w = ⊤) : Z = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  refine eq_bot_iff.2 fun x hx => ?_
  have hmem : ∀ {V : Scheme.{u}} (h : V ⟶ X), Z.comap h = ⊤ → ∀ v : V, h v ∉ Z.support := by
    intro V h hh v hv
    have : v ∈ ((Z.comap h).support : Set V) := by
      rwa [Scheme.IdealSheafData.support_comap]
    rwa [hh, Scheme.IdealSheafData.support_top] at this
  rcases hcov x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · exact hmem j hj y hx
  · exact hmem w hw z hx

/-- **Blow-up sequences over an open and closed subscheme.** Let `j : Y → X` and `w : W → X` be
open immersions with complementary images and `𝐁` a blow-up sequence starting with `X` without
empty blow-ups and with `(𝐁|_W)^red` empty. Then `𝐁` is the push-forward along `j` of
`(𝐁|_Y)^red`. -/
private theorem isPushforward_pullbackReduced_of_isCompl : ∀ {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) {Y W : Scheme.{u}} (j : Y ⟶ X) (w : W ⟶ X) [IsOpenImmersion j]
    [IsOpenImmersion w], (∀ x, x ∈ Set.range j ∨ x ∈ Set.range w) → (∀ y z, j y ≠ w z) →
    B.HasNoEmptyBlowups → B.pullbackReduced w = .nil W →
    ClosedBlowupSequence.IsPushforward j (B.pullbackReduced j) B := by
  intro X B
  induction B with
  | nil X => intros; trivial
  | cons Z B ih =>
    intro Y W j w _ _ hcov hdisj hB hw
    by_cases hZw : Z.comap w = ⊤
    swap
    · simp only [ClosedBlowupSequence.pullbackReduced, hZw, dite_false] at hw
      cases hw
    simp only [ClosedBlowupSequence.pullbackReduced, hZw, dite_true] at hw
    have hZj : ¬ Z.comap j = ⊤ := fun h => hB.1 (eq_top_of_comap_eq_top j w hcov h hZw)
    simp only [ClosedBlowupSequence.pullbackReduced, hZj, dite_false]
    refine ⟨rfl, ?_, ?_⟩
    · refine le_antisymm (Scheme.IdealSheafData.le_map_comap _ _) ?_
      refine le_of_comap_le_of_cover j w hcov (Scheme.IdealSheafData.comap_map_le _ _) ?_
      rw [hZw]; exact le_top
    · rw [eqToHom_refl, Category.id_comp]
      have sqj := Kollar.isPullback_canonicalLift_of_flat j Z
      have sqw := Kollar.isPullback_blowUpLift_of_flat w Z hZw
      have : IsOpenImmersion (canonicalLift j Z) :=
        MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqj ‹_›
      have : IsOpenImmersion
          (blowUpLift Z w (ClosedBlowupSequence.isCartierOver_of_comap_eq_top w Z hZw)) :=
        MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqw ‹_›
      refine ih _ _ (fun x => ?_) (fun y z hyz => ?_) hB.2 hw
      · rcases hcov (blowUpToBase Z x) with hx | hx
        · exact Or.inl (mem_range_of_isPullback sqj hx)
        · exact Or.inr (mem_range_of_isPullback sqw hx)
      · have h1 := congrArg (blowUpToBase Z) hyz
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase,
          blowUpLift_comp, Scheme.Hom.comp_apply] at h1
        exact hdisj _ _ h1

end OpenClosed

section Sibling

open MMP.Mori

/-- No irreducible component of `X` lies in a closed subset of pure codimension one. -/
private theorem not_subset_of_isPureCodimOne {X : Type*} [TopologicalSpace X]
    {S : Closeds X} (hS : MMP.Mori.IsPureCodimOne S) :
    ∀ Z ∈ irreducibleComponents X, ¬ Z ⊆ (S : Set X) := by
  intro Z hZ hsub
  let W : IrreducibleCloseds X := ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents Z hZ⟩
  have hmax : IsMax W := fun W' hW' => hZ.2 W'.isIrreducible hW'
  have h1 := hS W ⟨hsub, fun W' _ hW' => hmax hW'⟩
  rw [codimension_eq_coheight, Order.coheight_eq_zero.2 hmax] at h1
  exact zero_ne_one h1

/-- A smooth centre along which `I` has order `≥ m`, in a smooth scheme, lies in
`cosupp(I, m)`. -/
private theorem support_subset_cosupport {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme s) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) (a : MarkedIdeal X)
    (hord : OrderAlongGE a.I (Z.support : Set X) a.m) :
    (Z.support : Set X) ⊆ a.cosupport := by
  intro u hu
  change (a.m : ℕ∞) ≤ idealOrder _
  rw [natCast_le_idealOrder_iff']
  refine (stalk_le_pow_of_orderAlongGE s hX Z hZ a.I a.m hord u).trans ?_
  refine Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal fun h => ?_) a.m
  exact ((IdealSheafData.stalk_eq_top_iff_notMem_support Z u).1 h) hu

/-- A smooth blow-up sequence of order `≥ m` without empty blow-ups starting with a marked
triple of empty cosupport is empty. -/
private theorem eq_nil_of_cosupport_eq_empty {k : Type u} [Field k] {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
    (E : OrderedDivisor X) (hB : B.IsOrderGeMarkedTripleSeq s a E) (hne : B.HasNoEmptyBlowups)
    (ha : a.cosupport = ∅) : B = .nil X := by
  cases B with
  | nil => rfl
  | cons Z B =>
    obtain ⟨hT, hZ, -, -, hord, -⟩ := hB
    have hsub := support_subset_cosupport s hT.2.1 Z hZ a hord
    rw [ha, Set.subset_empty_iff] at hsub
    refine (hne.1 ?_).elim
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    exact SetLike.coe_injective hsub

section Dimension

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- If the stalks of `D` are generated by members of regular systems of parameters, the local
ring of `D` at a point has dimension one less than that of `Y`. -/
private theorem exists_ringKrullDim_stalk_subscheme (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    (s : D.subscheme) : ∃ m : ℕ, ringKrullDim (Y.presheaf.stalk (D.subschemeι s)) = m ∧
      ringKrullDim (D.subscheme.presheaf.stalk s) = (((m - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hz : D.subschemeι s ∈ D.support := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι]; exact ⟨s, rfl⟩
  obtain ⟨m, w, j, hw, hy⟩ := hD _ hz
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  refine ⟨m, hw.2, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv D s), hy]
  exact ringKrullDim_quotient_span_singleton_of_isRegularSystemOfParameters hw j

/-- On an equidimensional scheme of dimension `d` locally of finite type over a field, a
nonempty quasi-compact closed subscheme whose stalk ideals are generated by members of regular
systems of parameters is equidimensional of dimension `d - 1`. -/
private theorem equidimensional_and_topologicalKrullDim_subscheme {k : Type u} [Field k]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (he : Equidimensional Y) {d : ℕ}
    (hd : topologicalKrullDim Y = ((d : ℕ∞) : WithBot ℕ∞)) (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    [CompactSpace D.subscheme] [Nonempty D.subscheme] :
    Equidimensional D.subscheme ∧
      topologicalKrullDim D.subscheme = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hle : ∀ s,
      ringKrullDim (D.subscheme.presheaf.stalk s) ≤ (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    intro s
    obtain ⟨m, hm, hs⟩ := exists_ringKrullDim_stalk_subscheme D hD s
    have h1 : ringKrullDim (Y.presheaf.stalk (D.subschemeι s)) ≤ topologicalKrullDim Y := by
      rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      exact le_iSup (fun y => ringKrullDim (Y.presheaf.stalk y)) _
    rw [hm, hd] at h1
    have h2 : m ≤ d := by exact_mod_cast h1
    rw [hs]
    exact WithBot.coe_le_coe.2 (by exact_mod_cast Nat.sub_le_sub_right h2 1)
  have hcl : ∀ s : D.subscheme, IsClosed ({s} : Set D.subscheme) →
      ringKrullDim (D.subscheme.presheaf.stalk s) = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    intro s hs
    obtain ⟨m, hm, hs'⟩ := exists_ringKrullDim_stalk_subscheme D hD s
    have hy : IsClosed ({D.subschemeι s} : Set Y) := by
      simpa using D.subschemeι.isClosedEmbedding.isClosedMap _ hs
    have h1 := topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point sY _ hy
    rw [topologicalKrullDimAt_eq_of_equidimensional k Y sY he
      (d := d) (by rw [hd]; rfl), hm] at h1
    have h2 : m = d := by exact_mod_cast h1.symm
    rw [hs', h2]
  have hat : ∀ s : D.subscheme,
      topologicalKrullDimAt D.subscheme s = ((d - 1 : ℕ) : WithBot ℕ∞) := by
    intro s
    rw [topologicalKrullDimAt_eq_iInf_closedSpecializations (D.subschemeι ≫ sY) s]
    obtain ⟨s', hs'mem, hs'cl⟩ :=
      (isClosed_closure (s := ({s} : Set D.subscheme))).exists_closed_singleton
        ⟨s, subset_closure rfl⟩
    refine le_antisymm (iInf_le_of_le ⟨s', specializes_iff_mem_closure.2 hs'mem, hs'cl⟩
      (hcl s' hs'cl).le) (le_iInf fun x => (hcl x.1 x.2.2).ge)
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq k _ (D.subschemeι ≫ sY) hat, ?_⟩
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  obtain ⟨s0, -, hs0⟩ :=
    isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := D.subscheme))
  exact le_antisymm (iSup_le hle) (le_iSup_of_le s0 (hcl s0 hs0).ge)

end Dimension

section Hypersurface

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [LocallyOfFiniteType sX]

/-- At a point of a smooth hypersurface `H` of a smooth scheme, the stalk of `H` is generated by
one member of a regular system of parameters: `𝒪_{X,x} / H_x` is regular and `H_x` is a prime of
height one. -/
private theorem exists_stalk_eq_span_parameter_of_isSmoothHypersurface
    (hX : MMP.Mori.IsSmoothScheme sX) {H : X.IdealSheafData} (hH : IsSmoothHypersurface sX H) :
    ∀ x ∈ H.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x) (j : Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ IdealSheafData.stalk H x = Ideal.span {z j} := by
  intro x hx
  have : PerfectField k := PerfectField.ofCharZero
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  have : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).1 hX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsRegularLocalRing (X.presheaf.stalk x) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).mp inferInstance x
  have hq := MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_stalk sX H hH.1 hx
  have : (IdealSheafData.stalk H x).IsPrime := by
    have := IsRegularLocalRing.isDomain (X.presheaf.stalk x ⧸ IdealSheafData.stalk H x)
    exact (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance
  have hdim := MMP.Flips.ResolutionInputs.ringKrullDim_quotient_add_one_of_height_eq_one _
    (MMP.Flips.ResolutionInputs.height_stalk_eq_one_of_isPureCodimOne H hH.2 (x := x))
  obtain ⟨m, hm⟩ : ∃ m : ℕ,
      ringKrullDim (X.presheaf.stalk x ⧸ IdealSheafData.stalk H x) = m := by
    have hlt := ringKrullDim_lt_top (R := X.presheaf.stalk x ⧸ IdealSheafData.stalk H x)
    have h0 := ringKrullDim_nonneg_of_nontrivial
      (R := X.presheaf.stalk x ⧸ IdealSheafData.stalk H x)
    generalize ringKrullDim (X.presheaf.stalk x ⧸ IdealSheafData.stalk H x) = e at hlt h0 ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd hlt (by simp)
      | coe m => exact ⟨m, rfl⟩
  obtain ⟨xs, ys, hs, -, hI⟩ := MMP.Flips.ResolutionInputs.exists_flag_isRegularSystemOfParameters
    le_rfl hq hdim hq (r := 1) (m := m) le_rfl (by rw [← hdim, hm]; push_cast; ring) hm
  exact ⟨1 + m, Fin.append xs ys, Fin.castAdd m 0, hs, by rw [hI, Fin.append_left]; rfl⟩

end Hypersurface

/-- The empty ordered divisor on a smooth scheme is an ordered snc divisor. -/
private theorem isOrderedSNC_empty {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (hX : MMP.Mori.IsSmoothScheme sX) :
    (OrderedDivisor.empty X).IsOrderedSNC sX := by
  have : PerfectField k := PerfectField.ofCharZero
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  have : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).1 hX
  refine ⟨fun i => i.elim0, fun i => i.elim0, fun x => ?_⟩
  have : IsRegularLocalRing (X.presheaf.stalk x) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).mp inferInstance x
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
  exact ⟨n, z, fun i => i.1.elim0, hz, fun i => i.1.elim0, fun i => i.1.elim0⟩

/-- A point lies in the support of `I` exactly when `I` has order `≥ 1` there. -/
private theorem one_le_multAt_iff_mem_support {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    ((1 : ℕ) : ℕ∞) ≤ multAt I x ↔ x ∈ I.support := by
  change _ ≤ idealOrder _ ↔ _
  rw [natCast_le_idealOrder_iff', pow_one, ← not_iff_not,
    ← IdealSheafData.stalk_eq_top_iff_notMem_support]
  exact ⟨fun h => by_contra fun h' => h (IsLocalRing.le_maximalIdeal h'),
    fun h h' => (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h ▸ h'))⟩

/-- An ideal sheaf of maximal order `0` is the unit ideal. -/
private theorem eq_top_of_maxOrder_eq_zero {X : Scheme.{u}} {I : X.IdealSheafData}
    (h0 : maxOrder I = 0) : I = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  refine eq_bot_iff.2 fun x hx => ?_
  have hle := multAt_le_maxOrder I x
  rw [h0] at hle
  exact absurd (((one_le_multAt_iff_mem_support I x).2 hx).trans hle) (by simp)

/-- A nonempty smooth hypersurface of a triple of dimension `n` is equidimensional of dimension
`n - 1`. -/
private theorem equidimensional_and_topologicalKrullDim_of_isSmoothHypersurface {n : ℕ}
    {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞))
    {H : t.X.IdealSheafData} (hH : IsSmoothHypersurface t.sX H) [Nonempty H.subscheme] :
    Equidimensional H.subscheme ∧
      topologicalKrullDim H.subscheme = (((n - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨hchar, hsm, hlft, hqc, hequi, -, -⟩ := ht
  have := hchar
  have := hlft
  have := hqc
  have : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  have : CompactSpace t.X := QuasiCompact.compactSpace_of_compactSpace t.sX
  have : CompactSpace H.subscheme := QuasiCompact.compactSpace_of_compactSpace H.subschemeι
  exact equidimensional_and_topologicalKrullDim_subscheme t.sX hequi hdim H
    (exists_stalk_eq_span_parameter_of_isSmoothHypersurface hsm hH)

/-- An ideal containing the ideal of a smooth hypersurface `H` of a triple has maximal order
`≤ 1`: no irreducible component of `X` lies in `H`. -/
private theorem maxOrder_le_one_of_isSmoothHypersurface {t : FieldBlowupTriple.{u}}
    (ht : t ∈ triples) {H : t.X.IdealSheafData} (hH : IsSmoothHypersurface t.sX H)
    {J : H.subscheme.IdealSheafData} (hI : t.I = J.map H.subschemeι) : maxOrder t.I ≤ 1 := by
  obtain ⟨hchar, hsm, hlft, -, -, -, -⟩ := ht
  have := hchar
  have := hlft
  have : PerfectField t.k := PerfectField.ofCharZero
  have : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr inferInstance
  have : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  have : LocallyOfFinitePresentation (H.subschemeι ≫ t.sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := H.subschemeι ≫ t.sX)).mpr
      inferInstance
  have : Smooth (H.subschemeι ≫ t.sX) := (MMP.Mori.isSmoothScheme_iff _).1 hH.1
  have : ∀ x : t.X, IsRegularLocalRing (t.X.presheaf.stalk x) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk t.sX).mp
      inferInstance
  have : ∀ y : H.subscheme, IsRegularLocalRing (H.subscheme.presheaf.stalk y) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk
      (H.subschemeι ≫ t.sX)).mp inferInstance
  exact Kollar.maxOrder_le_one_of_eq_ker H J t.I (not_subset_of_isPureCodimOne hH.2) hI

end Sibling

/-! ### Dimension and generic points -/

section Geometry

/-- An ordered divisor without entries is the empty one. -/
private theorem eq_empty_of_s_eq_zero {X : Scheme.{u}} {E : OrderedDivisor X} (h : E.s = 0) :
    E = OrderedDivisor.empty X := by
  obtain ⟨s, E⟩ := E
  change s = 0 at h
  subst h
  simp only [OrderedDivisor.empty, OrderedDivisor.mk.injEq, heq_eq_eq, true_and]
  funext i; exact i.elim0

/-- An irreducible component of an equidimensional space has the dimension of the space. -/
private theorem topologicalKrullDim_eq_of_equidimensional {T : Type*} [TopologicalSpace T]
    (he : TopologicalSpace.Equidimensional T) {C : Set T} (hC : C ∈ irreducibleComponents T) :
    topologicalKrullDim C = topologicalKrullDim T := by
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents T]
  exact le_antisymm (le_iSup₂ (f := fun W (_ : W ∈ irreducibleComponents T) =>
    topologicalKrullDim W) C hC) (iSup₂_le fun W hW => (he W hW C hC).le)

/-- A nonempty scheme of finite type over a field has finite dimension. -/
private theorem exists_topologicalKrullDim_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = ((n : ℕ∞) : WithBot ℕ∞) := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace s).1 ‹_›
  have h1 := AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType k s
  have h2 : topologicalKrullDim X ≠ ⊥ := fun h =>
    ((topologicalKrullDim_eq_bot_iff_isEmpty X).1 h).false (Classical.arbitrary X)
  generalize topologicalKrullDim X = e at h1 h2 ⊢
  induction e using WithBot.recBotCoe with
  | bot => exact absurd rfl h2
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd rfl h1
    | coe n => exact ⟨n, rfl⟩

/-- A nonempty scheme of finite type over a field has a dimension. -/
private theorem hasDimensionIn_univ {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s] [Nonempty X] :
    HasDimensionIn X Set.univ := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq s
  exact ⟨n, trivial, hn⟩

/-- An inducing map does not lower the dimension of a subset. -/
private theorem topologicalKrullDim_le_image {Y X : Type*} [TopologicalSpace Y]
    [TopologicalSpace X] {f : Y → X} (hf : Topology.IsInducing f) (C : Set Y) :
    topologicalKrullDim C ≤ topologicalKrullDim (f '' C) := by
  let g : C → f '' C := fun x => ⟨f x, x, x.2, rfl⟩
  have hg : Topology.IsInducing g :=
    (Topology.IsInducing.subtypeVal.of_comp_iff).1 (hf.comp Topology.IsInducing.subtypeVal)
  exact hg.topologicalKrullDim_le

/-- A closed subset of an irreducible set `C` of dimension at most `d`, contained in `C` and
missing one of its points, has dimension `< d`. -/
private theorem topologicalKrullDim_lt_of_subset_of_notMem {T : Type*} [TopologicalSpace T]
    {C F : Set T} (hC : IsIrreducible C) (hF : IsClosed F) (hFC : F ⊆ C) {η : T} (hηC : η ∈ C)
    (hηF : η ∉ F) {d : ℕ} (hd : topologicalKrullDim C ≤ d) :
    topologicalKrullDim F < d := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · rw [show topologicalKrullDim (∅ : Set T) = ⊥ from
      (topologicalKrullDim_eq_bot_iff_isEmpty _).2 (Set.isEmpty_coe_sort.2 rfl)]
    exact WithBot.bot_lt_coe _
  have hinter : C ∩ F = F := Set.inter_eq_right.2 hFC
  obtain ⟨h1, h2⟩ := topologicalKrullDim_inter_le_pred_of_not_subset hC hF
    (fun h => hηF (h hηC)) (by rwa [hinter]) hd
  rw [hinter] at h2
  exact h2.trans_lt (by exact_mod_cast (by omega : d - 1 < d))

/-- If a closed subscheme `Y` of an equidimensional `X` contains an irreducible component of `X`,
then `dim Y = dim X`. -/
private theorem topologicalKrullDim_eq_of_subset_range {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsClosedImmersion j] (hXe : TopologicalSpace.Equidimensional X) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hZj : Z ⊆ Set.range j) :
    topologicalKrullDim Y = topologicalKrullDim X := by
  refine le_antisymm j.isEmbedding.isInducing.topologicalKrullDim_le ?_
  rw [← topologicalKrullDim_eq_of_equidimensional hXe hZ,
    IsHomeomorph.topologicalKrullDim_eq _ j.isEmbedding.toHomeomorph.isHomeomorph]
  exact (Topology.IsEmbedding.inclusion hZj).isInducing.topologicalKrullDim_le

/-- **Codimension zero.** If `Y ⊆ X` is a closed subscheme of a smooth scheme over a field, both
equidimensional of the same finite dimension, then `Y` is open in `X`. -/
private theorem isOpen_range_of_topologicalKrullDim_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (hXe : TopologicalSpace.Equidimensional X)
    (hYe : TopologicalSpace.Equidimensional Y) (j : Y ⟶ X) [IsClosedImmersion j] {n : ℕ}
    (hX : topologicalKrullDim X = ((n : ℕ∞) : WithBot ℕ∞))
    (hY : topologicalKrullDim Y = ((n : ℕ∞) : WithBot ℕ∞)) : IsOpen (Set.range j) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨y, rfl⟩
  have hC := irreducibleComponent_mem_irreducibleComponents y
  have hF : IsClosed (j '' irreducibleComponent y) :=
    j.isClosedEmbedding.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ hC)
  have hFirr : IsIrreducible (j '' irreducibleComponent y) :=
    hC.1.image j j.continuous.continuousOn
  obtain ⟨D, hD, hFD⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hFirr
  have hDsub : D ⊆ Set.range j := by
    by_contra hns
    obtain ⟨η, hηD, hηr⟩ := Set.not_subset.1 hns
    have hηF : η ∉ j '' irreducibleComponent y := fun ⟨c, _, hc⟩ => hηr ⟨c, hc⟩
    have hDd : topologicalKrullDim D ≤ (n : WithBot ℕ∞) := by
      rw [topologicalKrullDim_eq_of_equidimensional hXe hD, hX]; rfl
    have hlt := topologicalKrullDim_lt_of_subset_of_notMem hD.1 hF hFD
      hηD hηF hDd
    have hge : (n : WithBot ℕ∞) ≤ topologicalKrullDim (j '' irreducibleComponent y) := by
      have := topologicalKrullDim_le_image j.isEmbedding.isInducing (irreducibleComponent y)
      rwa [topologicalKrullDim_eq_of_equidimensional hYe hC, hY] at this
    exact absurd (hge.trans_lt hlt) (lt_irrefl _)
  exact ⟨D, hDsub, MMP.Flips.ResolutionInputs.isOpen_of_mem_irreducibleComponents_of_smooth sX hD,
    hFD ⟨y, mem_irreducibleComponent, rfl⟩⟩

/-- The image of an ideal sheaf nonzero at the generic points under a closed immersion is nonzero
at the generic points. -/
private theorem isNonzeroAtGenericPoints_map {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsClosedImmersion j] {I : Y.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) :
    IsNonzeroAtGenericPoints (I.map j) := by
  intro η hη h0
  by_cases hηr : η ∈ Set.range j
  · obtain ⟨ξ, rfl⟩ := hηr
    have hξ : closure ({ξ} : Set Y) ∈ irreducibleComponents Y := by
      refine ⟨isIrreducible_singleton.closure, fun C hC hsub => ?_⟩
      have h1 : closure ({j ξ} : Set X) ⊆ closure (j '' C) :=
        closure_mono (Set.singleton_subset_iff.2 ⟨ξ, hsub (subset_closure rfl), rfl⟩)
      have h2 := hη.2 (hC.image j j.continuous.continuousOn).closure h1
      intro c hc
      have hc' : j c ∈ closure ({j ξ} : Set X) := h2 (subset_closure ⟨c, hc, rfl⟩)
      rwa [j.isEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
    refine hI ξ hξ ?_
    rw [← I.comap_map_of_isClosedImmersion j, IdealSheafData.stalk_comap, h0, Ideal.map_bot]
  · have hns : η ∉ (I.map j).support := by
      intro h
      rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_map,
        TopologicalSpace.Closeds.coe_closure] at h
      exact hηr (closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact ⟨y, rfl⟩)
        j.isClosedEmbedding.isClosed_range h)
    rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hns] at h0
    exact top_ne_bot h0

end Geometry

/-! ### The canonical `𝓑𝓜𝓞_{·,1}` -/

section BMO

/-- `𝓑𝓜𝓞` deletes empty blow-ups. -/
private theorem hasNoEmptyBlowups_bmoFamily (n m : ℕ) (t : MarkedTriple.{u}) :
    (bmoFamily n m t).HasNoEmptyBlowups := by
  unfold bmoFamily bmoFunctor
  exact ClosedBlowupSequence.hasNoEmptyBlowups_reduction _

/-- `𝓑𝓜𝓞` applied to equal marked triples, as a heterogeneous equality. -/
private theorem bmoFamily_congr {n m : ℕ} {t t' : MarkedTriple.{u}} (e : t = t') :
    bmoFamily n m t ≍ bmoFamily n m t' := by
  subst e; rfl

/-- A blow-up sequence on the empty scheme without empty blow-ups is empty. -/
private theorem eq_nil_of_isEmpty {X : Scheme.{u}} [IsEmpty X] {B : ClosedBlowupSequence X}
    (hB : B.HasNoEmptyBlowups) : B = .nil X := by
  cases B with
  | nil => rfl
  | cons Z B =>
    refine (hB.1 ?_).elim
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    exact eq_bot_iff.2 fun x _ => isEmptyElim x

/-- An open immersion is an open cover map. -/
private theorem isOpenCoverMap_of_isOpenImmersion {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] : IsOpenCoverMap f :=
  ⟨1, fun _ => ⊤, fun a b h => (h (Subsingleton.elim a b)).elim, by simp,
    fun _ => inferInstance⟩

/-- A triple on a nonempty scheme, marked by `1`, lies in the domain of `𝓑𝓜𝓞_1`. -/
private theorem mem_markedTriplesOfDim {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    [Nonempty t.X] : (⟨t, 1⟩ : MarkedTriple.{u}) ∈ markedTriplesOfDim Set.univ 1 := by
  have := ht.2.2.1
  have := ht.2.2.2.1
  exact ⟨ht, rfl, hasDimensionIn_univ t.sX⟩

/-- `𝓑𝓜𝓞_1` commutes with smooth surjections. -/
private theorem bmoFamily_pullback_of_surjective {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    [Nonempty t.X] {Y : Scheme.{u}} [Nonempty Y] (h : Y ⟶ t.X) (hs : Smooth h)
    (hsu : Surjective h) (hY : t.pullback h ∈ triples) :
    bmoFamily (dimNat Y) 1 ⟨t.pullback h, 1⟩ =
      (bmoFamily (dimNat t.X) 1 ⟨t, 1⟩).pullback h := by
  obtain ⟨F, hF, -, hc, -⟩ := exists_isOrderReductionFunctorMarked_bmoFamily.{u} 1 le_rfl
  have hm := mem_markedTriplesOfDim ht
  have hmY : (⟨t.pullback h, 1⟩ : MarkedTriple.{u}) ∈ markedTriplesOfDim Set.univ 1 :=
    @mem_markedTriplesOfDim (t.pullback h) hY ‹Nonempty Y›
  exact (hF _ hmY).symm.trans ((hc.1 ⟨t, 1⟩ hm Y h hs hsu hY.2.2.1 hY.2.2.2.1 hmY).trans
    (by rw [hF _ hm]))

/-- `𝓑𝓜𝓞_1` commutes with smooth morphisms, up to deleting empty blow-ups. -/
private theorem bmoFamily_pullback {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    [Nonempty t.X] {Y : Scheme.{u}} [Nonempty Y] (h : Y ⟶ t.X) (hs : Smooth h)
    (hY : t.pullback h ∈ triples) :
    bmoFamily (dimNat Y) 1 ⟨t.pullback h, 1⟩ =
      (bmoFamily (dimNat t.X) 1 ⟨t, 1⟩).pullbackReduced h := by
  obtain ⟨F, hF, -, hc, -⟩ := exists_isOrderReductionFunctorMarked_bmoFamily.{u} 1 le_rfl
  have hm := mem_markedTriplesOfDim ht
  have hmY : (⟨t.pullback h, 1⟩ : MarkedTriple.{u}) ∈ markedTriplesOfDim Set.univ 1 :=
    @mem_markedTriplesOfDim (t.pullback h) hY ‹Nonempty Y›
  rw [← ClosedBlowupSequence.reduction_pullback]
  exact (hF _ hmY).symm.trans ((hc.2 ⟨t, 1⟩ hm Y h hs hY.2.2.1 hY.2.2.2.1 hmY).trans
    (by rw [hF _ hm]))

/-- `𝓑𝓜𝓞_1` of the unit ideal is empty. -/
private theorem bmoFamily_eq_nil_of_I_eq_top {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    (htop : t.I = ⊤) : bmoFamily (dimNat t.X) 1 ⟨t, 1⟩ = .nil t.X := by
  by_cases hX : IsEmpty t.X
  · exact eq_nil_of_isEmpty (hasNoEmptyBlowups_bmoFamily _ _ _)
  rw [not_isEmpty_iff] at hX
  have hm := mem_markedTriplesOfDim ht
  obtain ⟨F, hF, -⟩ := exists_isOrderReductionFunctorMarked_bmoFamily.{u} 1 le_rfl
  refine (hF _ hm).symm.trans ?_
  refine eq_nil_of_cosupport_eq_empty _ _ _ _ (F.isOrderGeMarkedTripleSeq _ hm)
    (F.hasNoEmptyBlowups _ hm) (Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_)
  have hy' : ((1 : ℕ) : ℕ∞) ≤ multAt t.I y := hy
  have := (one_le_multAt_iff_mem_support t.I y).1 hy'
  simp [htop, ← SetLike.mem_coe] at this

/-- The empty sequence is the push-forward of the empty sequence. -/
private theorem isPushforward_of_eq_nil {S X : Scheme.{u}} (j : S ⟶ X)
    {B : ClosedBlowupSequence S} {B' : ClosedBlowupSequence X} (h : B = .nil S)
    (h' : B' = .nil X) : ClosedBlowupSequence.IsPushforward j B B' := by
  subst h h'; trivial

/-- Rewriting the sequence being pushed forward. -/
private theorem isPushforward_congr_left {S X : Scheme.{u}} {j : S ⟶ X}
    {B₁ B₂ : ClosedBlowupSequence S} {B : ClosedBlowupSequence X} (e : B₁ = B₂)
    (h : ClosedBlowupSequence.IsPushforward j B₂ B) : ClosedBlowupSequence.IsPushforward j B₁ B :=
  e ▸ h

/-- The ambient triple of closed-embedding data is a triple. -/
private theorem ambientTriple_mem_triples (d : ClosedEmbeddingData.{u}) (hE : d.E.s = 0)
    (hY : d.embeddedTriple ∈ triples) (hXs : MMP.Mori.IsSmoothScheme d.sX)
    (hXf : LocallyOfFiniteType d.sX) (hXq : QuasiCompact d.sX) (hXe : Equidimensional d.X) :
    d.ambientTriple ∈ triples := by
  have : IsClosedImmersion d.j := d.isClosedImmersion
  have : CharZero d.k := hY.1
  refine ⟨hY.1, hXs, hXf, hXq, hXe, ?_, ?_⟩
  · change IsNonzeroAtGenericPoints d.IX
    rw [d.IX_eq]
    exact isNonzeroAtGenericPoints_map d.j hY.2.2.2.2.2.1
  · change d.E.IsOrderedSNC d.sX
    rw [eq_empty_of_s_eq_zero hE]
    exact isOrderedSNC_empty d.sX hXs

/-- The ideal on `X` restricts to the ideal on `Y`. -/
private theorem comap_IX (d : ClosedEmbeddingData.{u}) : d.IX.comap d.j = d.IY := by
  have : IsClosedImmersion d.j := d.isClosedImmersion
  rw [d.IX_eq]
  exact Scheme.IdealSheafData.comap_map_of_isClosedImmersion _ _

/-- With `Y` empty both sequences are empty. -/
private theorem isPushforward_of_isEmpty (d : ClosedEmbeddingData.{u}) (hE : d.E.s = 0)
    (hY : d.embeddedTriple ∈ triples) (hXs : MMP.Mori.IsSmoothScheme d.sX)
    (hXf : LocallyOfFiniteType d.sX) (hXq : QuasiCompact d.sX) (hXe : Equidimensional d.X)
    [IsEmpty d.Y] :
    ClosedBlowupSequence.IsPushforward d.j
      (bmoFamily (dimNat d.Y) 1 ⟨d.embeddedTriple, 1⟩)
      (bmoFamily (dimNat d.X) 1 ⟨d.ambientTriple, 1⟩) := by
  have : IsClosedImmersion d.j := d.isClosedImmersion
  have htop : d.IX = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    refine eq_bot_iff.2 fun x hx => ?_
    rw [← SetLike.mem_coe, d.IX_eq, Scheme.IdealSheafData.support_map,
      TopologicalSpace.Closeds.coe_closure] at hx
    have : (d.j '' (d.IY.support : Set d.Y)) = ∅ := by
      rw [Set.image_eq_empty]; exact Set.eq_empty_of_isEmpty _
    rwa [this, closure_empty] at hx
  have : IsEmpty (⟨d.embeddedTriple, 1⟩ : MarkedTriple.{u}).X := ‹IsEmpty d.Y›
  exact isPushforward_of_eq_nil d.j (eq_nil_of_isEmpty (hasNoEmptyBlowups_bmoFamily _ _ _))
    (bmoFamily_eq_nil_of_I_eq_top (t := d.ambientTriple)
      (ambientTriple_mem_triples d hE hY hXs hXf hXq hXe) (show d.ambientTriple.I = ⊤ from htop))

end BMO

/-! ### Codimension zero -/

/-- **Codimension `0`**: `Y` is open and closed in `X`, every centre of `𝓑𝓜𝓞(X)` lies over `Y`,
and `𝓑𝓜𝓞(Y)` is the restriction of `𝓑𝓜𝓞(X)`. -/
private theorem isPushforward_of_dimNat_eq (d : ClosedEmbeddingData.{u})
    (hE : d.E.s = 0) (hY : d.embeddedTriple ∈ triples)
    (hXs : MMP.Mori.IsSmoothScheme d.sX) (hXf : LocallyOfFiniteType d.sX)
    (hXq : QuasiCompact d.sX) (hXe : Equidimensional d.X) [Nonempty d.Y]
    (hc : dimNat d.X = dimNat d.Y) :
    ClosedBlowupSequence.IsPushforward d.j
      (bmoFamily (dimNat d.Y) 1 ⟨d.embeddedTriple, 1⟩)
      (bmoFamily (dimNat d.X) 1 ⟨d.ambientTriple, 1⟩) := by
  have : IsClosedImmersion d.j := d.isClosedImmersion
  have hXt := ambientTriple_mem_triples d hE hY hXs hXf hXq hXe
  obtain ⟨hchar, hYs, hYf, hYq, hYe, -, -⟩ := id hY
  have : CharZero d.k := hchar
  have : Smooth d.sX := MMP.Mori.IsSmoothScheme.smooth hXs
  have : Nonempty d.X := ⟨d.j (Classical.arbitrary _)⟩
  have : Nonempty d.ambientTriple.X := (inferInstance : Nonempty d.X)
  have : LocallyOfFiniteType (d.j ≫ d.sX) := hYf
  have : QuasiCompact (d.j ≫ d.sX) := hYq
  obtain ⟨n, hnX⟩ := exists_topologicalKrullDim_eq d.sX
  obtain ⟨nY, hnY⟩ := exists_topologicalKrullDim_eq (d.j ≫ d.sX)
  obtain rfl : n = nY := by rwa [← dimNat_eq hnX, ← dimNat_eq hnY]
  have hopen := isOpen_range_of_topologicalKrullDim_eq (Y := d.Y) d.sX hXe hYe d.j hnX hnY
  let U : d.X.Opens := ⟨Set.range d.j, hopen⟩
  let W : d.X.Opens := ⟨(Set.range d.j)ᶜ, d.j.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  -- `τ` is an open immersion: an isomorphism onto the reduced open subscheme `U`
  have hjU : Set.range d.j ⊆ Set.range U.ι := by rw [Scheme.Opens.range_ι]; rfl
  let j' := IsOpenImmersion.lift U.ι d.j hjU
  have hj' : j' ≫ U.ι = d.j := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (j' ≫ U.ι) := by rw [hj']; infer_instance
  have : IsClosedImmersion j' := IsClosedImmersion.of_comp j' U.ι
  have : Surjective j' := ⟨fun x => by
    obtain ⟨y, hy⟩ := x.2
    refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hj', hy]; rfl⟩
  have := isReduced_of_isSmoothScheme d.sX hXs
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have : IsIso j' := isIso_of_isClosedImmersion_of_surjective j'
  have : IsOpenImmersion d.j := by rw [← hj']; infer_instance
  have hjs : Smooth d.j := inferInstance
  have hws : Smooth W.ι := inferInstance
  -- `𝓑𝓜𝓞(Y)` is the restriction of `𝓑𝓜𝓞(X)`
  have hpb : d.ambientTriple.pullback d.j = d.embeddedTriple := by
    change FieldBlowupTriple.mk ⟨d.Y, d.IX.comap d.j, d.E.comap d.j⟩ d.k (d.j ≫ d.sX) =
      FieldBlowupTriple.mk ⟨d.Y, d.IY, d.E.comap d.j⟩ d.k (d.j ≫ d.sX)
    rw [comap_IX]
  have hYt : d.ambientTriple.pullback d.j ∈ triples := by rwa [hpb]
  have h1 : bmoFamily (dimNat d.Y) 1 ⟨d.embeddedTriple, 1⟩ =
      (bmoFamily (dimNat d.X) 1 ⟨d.ambientTriple, 1⟩).pullbackReduced d.j := by
    refine eq_of_heq ((bmoFamily_congr ?_).trans
      (heq_of_eq (bmoFamily_pullback hXt (Y := d.Y) d.j hjs hYt)))
    rw [hpb]
  refine isPushforward_congr_left h1 ?_
  refine isPushforward_pullbackReduced_of_isCompl _ d.j W.ι (fun x => ?_) (fun y z hyz => ?_)
    (hasNoEmptyBlowups_bmoFamily _ _ _) ?_
  · by_cases hx : x ∈ Set.range d.j
    · exact Or.inl hx
    · exact Or.inr (by rwa [Scheme.Opens.range_ι])
  · have : W.ι z ∈ W := by
      have : W.ι z ∈ Set.range W.ι := ⟨z, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    exact this ⟨y, hyz⟩
  · by_cases hW : IsEmpty W.toScheme
    · exact pullbackReduced_eq_nil_of_isEmpty _ _
    rw [not_isEmpty_iff] at hW
    have hWt : d.ambientTriple.pullback W.ι ∈ triples :=
      pullback_mem_triples_of_isOpenCoverMap _ hXt W.ι (isOpenCoverMap_of_isOpenImmersion W.ι)
    refine (bmoFamily_pullback hXt W.ι hws hWt).symm.trans ?_
    refine bmoFamily_eq_nil_of_I_eq_top (t := d.ambientTriple.pullback W.ι) hWt ?_
    change d.IX.comap W.ι = ⊤
    refine top_le_iff.1 ((le_of_eq ?_).trans (Scheme.IdealSheafData.comap_mono W.ι
      (show d.j.ker ≤ d.IX from ?_)))
    · symm
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      refine eq_bot_iff.2 fun z hz => ?_
      have hz2 : z ∈ ((d.j.ker.comap W.ι).support : Set W.toScheme) := hz
      have hz' : W.ι z ∈ (d.j.ker.support : Set d.X) := by
        rwa [Scheme.IdealSheafData.support_comap] at hz2
      rw [Scheme.Hom.support_ker, d.j.isClosedEmbedding.isClosed_range.closure_eq] at hz'
      have : W.ι z ∈ Set.range W.ι := ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι] at this
      exact (this hz').elim
    · rw [d.IX_eq, ← Scheme.IdealSheafData.map_bot]
      exact Scheme.IdealSheafData.map_mono d.j bot_le

/-! ### Positive codimension -/

section Positive

open Limits

/-- **Local sections cutting out smooth hypersurfaces through `Y`.** If the ideal `I_Y` of a
closed subscheme of a smooth scheme is not contained in `𝔪_x²` at any point of `Y`, every point
of `X` has an affine neighbourhood `W` with a nonzerodivisor `f ∈ I_Y(W)` whose zero scheme is
smooth. -/
private theorem exists_affine_smooth_section {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (J : X.IdealSheafData)
    (hJ : ∀ x ∈ J.support,
      ¬ IdealSheafData.stalk J x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2)
    (x : X) :
    ∃ (W : X.affineOpens) (_ : x ∈ W.1) (f : Γ(X, W.1)),
      f ∈ J.ideal W ∧ f ∈ nonZeroDivisors Γ(X, W.1) ∧
      Smooth (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫
        W.2.isoSpec.inv ≫ W.1.ι ≫ sX) := by
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  by_cases hx : x ∈ J.support
  · have hle1 : IdealSheafData.stalk J x ≤ IsLocalRing.maximalIdeal _ :=
      IsLocalRing.le_maximalIdeal fun h =>
        ((IdealSheafData.stalk_eq_top_iff_notMem_support _ _).1 h) hx
    obtain ⟨h, hh, hnot⟩ := exists_mem_ideal_germ_notMem J hU₀ hxU₀ (hJ x hx)
    have hmem : X.presheaf.germ U₀ x hxU₀ h ∈ IsLocalRing.maximalIdeal _ := hle1 <| by
      rw [IdealSheafData.stalk_eq_map_germ J x ⟨U₀, hU₀⟩ hxU₀]
      exact Ideal.mem_map_of_mem _ hh
    obtain ⟨V, hxV, g, hgerm, hg, hs, -⟩ :=
      MMP.exists_isAffineOpen_smooth_zeroLocus_of_mem_maximalIdeal_notMem_sq sX x _ hmem hnot
    obtain ⟨W₀, hxW₀, iV, iU, heqW⟩ := X.presheaf.germ_eq x hxV hxU₀ g h hgerm
    obtain ⟨a, haW, hxa⟩ := V.2.exists_basicOpen_le (V := W₀ ⊓ U₀) ⟨x, hxW₀, hxU₀⟩ hxV
    have haU₀ : X.basicOpen a ≤ U₀ := haW.trans inf_le_right
    have hres : X.presheaf.map (homOfLE (X.basicOpen_le a)).op g =
        X.presheaf.map (homOfLE haU₀).op h := by
      have := congrArg (X.presheaf.map (homOfLE (haW.trans inf_le_left)).op) heqW
      rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp] at this
    obtain ⟨hnzd, hsm⟩ := restrict_basicOpen sX V.2 a g hg hs
    refine ⟨⟨_, V.2.basicOpen a⟩, hxa, _, ?_, hnzd, hsm⟩
    rw [hres]
    exact J.ideal_le_comap_ideal (U := ⟨_, V.2.basicOpen a⟩) (V := ⟨U₀, hU₀⟩) haU₀ hh
  · have hA : IdealSheafData.stalk J x = ⊤ :=
      (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hx
    obtain ⟨h, hh, hu⟩ := exists_mem_ideal_germ_notMem J hU₀ hxU₀
      (P := IsLocalRing.maximalIdeal _) (by simpa [hA] using Ideal.IsMaximal.ne_top inferInstance)
    obtain ⟨a, hah, hxa⟩ := hU₀.exists_basicOpen_le
      ⟨x, (X.mem_basicOpen h x hxU₀).2 (IsLocalRing.notMem_maximalIdeal.1 hu)⟩ hxU₀
    have hfu := isUnit_map_of_le_basicOpen h (X.basicOpen_le a) hah
    exact ⟨⟨_, hU₀.basicOpen a⟩, hxa, _,
      J.ideal_le_comap_ideal (U := ⟨_, hU₀.basicOpen a⟩) (V := ⟨U₀, hU₀⟩) (X.basicOpen_le a) hh,
      hfu.mem_nonZeroDivisors, smooth_of_isUnit hfu _⟩

/-- **Order one along a smooth subscheme.** If `Y ⊆ X` is a smooth closed subscheme of a smooth
scheme over a field of characteristic `0` containing no irreducible component of `X`, the ideal
of `Y` is not contained in `𝔪_x²` at any point `x` of `Y`. -/
private theorem stalk_ker_not_le_maximalIdeal_sq {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (j : Y ⟶ X) [IsClosedImmersion j]
    (hY : Smooth (j ≫ sX)) (hcomp : ∀ Z ∈ irreducibleComponents X, ¬ Z ⊆ Set.range j) :
    ∀ x ∈ j.ker.support,
      ¬ IdealSheafData.stalk j.ker x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 := by
  intro x _ hle
  have : PerfectField k := PerfectField.ofCharZero
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).mp inferInstance
  have : Smooth (j.ker.subschemeι ≫ sX) := by
    change Smooth (j.imageι ≫ sX)
    rw [show j.imageι = inv j.toImage ≫ j from
      (IsIso.eq_inv_comp _).2 (Scheme.Hom.toImage_imageι _), Category.assoc]
    infer_instance
  have : ∀ y : j.ker.subscheme, IsRegularLocalRing (j.ker.subscheme.presheaf.stalk y) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk
      (j.ker.subschemeι ≫ sX)).mp inferInstance
  have hsupp : (j.ker.support : Set X) = Set.range j := by
    rw [Scheme.Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq]
  have hmax := Kollar.maxOrder_le_one_of_eq_ker j.ker ⊥ j.ker (hsupp ▸ hcomp) (by
    rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι])
  have h2 : ((2 : ℕ) : ℕ∞) ≤ multAt j.ker x := (natCast_le_idealOrder_iff' _ 2).2 hle
  exact absurd (h2.trans ((multAt_le_maxOrder _ x).trans hmax)) (by decide)

/-- `𝓑𝓜𝓞_{d,ν}` computed from `(𝓑𝓞_e)_{e ≤ m}` is the canonical one for `d ≤ m`. -/
private theorem bmoFamilyOf_eq {m d : ℕ} (hd : d ≤ m) (ν : ℕ) (t : MarkedTriple.{u}) :
    bmoFamilyOf (boFamilyUpTo m) m d ν t = bmoFamily d ν t := by
  simp only [bmoFamilyOf, hd, if_true, bmoFamily]
  congr 1
  funext e μ s
  simp only [UnmarkedFamily.truncate]
  split_ifs with he
  · rw [boFamilyUpTo_of_le (he.trans hd), boFamilyUpTo_of_le he]
  · rfl

/-- `𝓑𝓜𝓞` built from `(𝓑𝓞_e)_{e ≤ m}` is a marked order-reduction family on `0, …, m`. -/
private theorem isMarkedOrderReductionFamily_bmoFamilyOf (m : ℕ) :
    IsMarkedOrderReductionFamily.{u} 0 m (bmoFamilyOf (boFamilyUpTo m) m) := by
  intro μ hμ
  obtain ⟨F, hF, h⟩ := isMarkedOrderReductionFamily_bmoFamily.{u} m μ hμ
  refine ⟨F, fun t ht => (hF t ht).trans ?_, h⟩
  obtain ⟨e, he, hX⟩ := ht.2.2
  exact (bmoFamilyOf_eq (by rw [dimNat_eq hX]; exact he.2) μ t).symm

/-- `𝓑𝓞_{m+1,1}` is `𝓑𝓞_{m+1}` built from the marked family in dimensions `≤ m`. -/
private theorem boFamily_succ (m : ℕ) (t : FieldBlowupTriple.{u}) :
    boFamily (m + 1) 1 t = boFunctor (bmoFamilyOf (boFamilyUpTo m) m) (m + 1) 1 t := by
  change boFamilyUpTo (m + 1) (m + 1) 1 t = _
  simp [boFamilyUpTo]

/-- Rewriting the push-forward sequence. -/
private theorem isPushforward_congr_right {S X : Scheme.{u}} {j : S ⟶ X}
    {B : ClosedBlowupSequence S} {B₁ B₂ : ClosedBlowupSequence X} (e : B₁ = B₂)
    (h : ClosedBlowupSequence.IsPushforward j B B₂) : ClosedBlowupSequence.IsPushforward j B B₁ :=
  e ▸ h

/-- **Positive codimension**: reduce, on a surjective open cover map, to a smooth hypersurface
containing `Y` and compose with the induction hypothesis. -/
private theorem isPushforward_of_dimNat_ne (d : ClosedEmbeddingData.{u})
    (hE : d.E.s = 0) (hY : d.embeddedTriple ∈ triples)
    (hXs : MMP.Mori.IsSmoothScheme d.sX) (hXf : LocallyOfFiniteType d.sX)
    (hXq : QuasiCompact d.sX) (hXe : Equidimensional d.X) [Nonempty d.Y]
    (hc : dimNat d.X ≠ dimNat d.Y)
    (ih : ∀ d' : ClosedEmbeddingData.{u}, dimNat d'.X < dimNat d.X → d'.E.s = 0 →
      d'.embeddedTriple ∈ triples → MMP.Mori.IsSmoothScheme d'.sX →
      LocallyOfFiniteType d'.sX → QuasiCompact d'.sX → Equidimensional d'.X →
      ClosedBlowupSequence.IsPushforward d'.j
        (bmoFamily (dimNat d'.Y) 1 ⟨d'.embeddedTriple, 1⟩)
        (bmoFamily (dimNat d'.X) 1 ⟨d'.ambientTriple, 1⟩)) :
    ClosedBlowupSequence.IsPushforward d.j
      (bmoFamily (dimNat d.Y) 1 ⟨d.embeddedTriple, 1⟩)
      (bmoFamily (dimNat d.X) 1 ⟨d.ambientTriple, 1⟩) := by
  have : IsClosedImmersion d.j := d.isClosedImmersion
  have hXt := ambientTriple_mem_triples d hE hY hXs hXf hXq hXe
  obtain ⟨hchar, hYs, hYf, hYq, -⟩ := id hY
  have : CharZero d.k := hchar
  have : Smooth d.sX := MMP.Mori.IsSmoothScheme.smooth hXs
  have : Nonempty d.X := ⟨d.j (Classical.arbitrary _)⟩
  have : Nonempty d.ambientTriple.X := (inferInstance : Nonempty d.X)
  have : Nonempty d.embeddedTriple.X := (inferInstance : Nonempty d.Y)
  have : LocallyOfFiniteType (d.j ≫ d.sX) := hYf
  have : QuasiCompact (d.j ≫ d.sX) := hYq
  -- the unit ideal
  by_cases hIX : d.IX = ⊤
  · have hIY : d.IY = ⊤ := by rw [← comap_IX, hIX, Scheme.IdealSheafData.comap_top]
    exact isPushforward_of_eq_nil d.j (bmoFamily_eq_nil_of_I_eq_top (t := d.embeddedTriple) hY hIY)
      (bmoFamily_eq_nil_of_I_eq_top (t := d.ambientTriple) hXt hIX)
  -- dimensions
  obtain ⟨n, hnX⟩ := exists_topologicalKrullDim_eq d.sX
  obtain ⟨nY, hnY⟩ := exists_topologicalKrullDim_eq (d.j ≫ d.sX)
  have hnYn : nY < n := by
    have hle : topologicalKrullDim d.Y ≤ topologicalKrullDim d.X :=
      d.j.isEmbedding.isInducing.topologicalKrullDim_le
    rw [hnX, hnY] at hle
    have h1 : nY ≤ n := by exact_mod_cast hle
    have h2 : n ≠ nY := by rwa [← dimNat_eq hnX, ← dimNat_eq hnY]
    omega
  -- no irreducible component of `X` lies in `Y`, so `I_Y` has order one along `Y`
  set J := d.j.ker
  have hJ1 := stalk_ker_not_le_maximalIdeal_sq d.sX d.j
    (MMP.Mori.IsSmoothScheme.smooth (f := d.j ≫ d.sX) hYs) fun Z hZ hsub => by
      have := topologicalKrullDim_eq_of_subset_range d.j hXe hZ hsub
      rw [hnX, hnY] at this
      have : nY = n := by exact_mod_cast this
      omega
  -- local smooth hypersurfaces containing `Y`
  have hloc : ∀ x : d.X, ∃ U : d.X.affineOpens, x ∈ U.1 ∧
      ∃ H : U.1.toScheme.IdealSheafData, IsSmoothHypersurface (U.1.ι ≫ d.sX) H ∧
        H ≤ J.comap U.1.ι := fun x => by
    obtain ⟨U, hxU, f, hf, hnzd, hsm⟩ := exists_affine_smooth_section d.sX J hJ1 x
    obtain ⟨H, hH, hHle⟩ := exists_isSmoothHypersurface_of_section d.sX U J f hf hnzd hsm
    exact ⟨U, hxU, H, hH, hHle⟩
  choose U hxU H hH hHle using hloc
  have : CompactSpace d.X := (quasiCompact_iff_compactSpace d.sX).1 ‹_›
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => ((U x).1 : Set d.X))
    (fun x => (U x).1.isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  let e := s.equivFin.symm
  let V : Fin s.card → Scheme.{u} := fun i => (U (e i).1).1.toScheme
  let jV : ∀ i, V i ⟶ d.X := fun i => (U (e i).1).1.ι
  let g : (∐ V) ⟶ d.X := Sigma.desc jV
  have hg : IsOpenCoverMap g := isOpenCoverMap_sigmaDesc V jV
  have hgs : Surjective g := ⟨fun x => by
    obtain ⟨x', hx', hxU'⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    let i := s.equivFin ⟨x', hx'⟩
    have hei : (e i).1 = x' := by simp [e, i]
    have hx : x ∈ ((U (e i).1).1 : Set d.X) := by rwa [hei]
    refine ⟨Sigma.ι V i (show V i from ⟨x, hx⟩), ?_⟩
    change (Sigma.ι V i ≫ g) _ = x
    rw [Sigma.ι_desc]
    rfl⟩
  have : Smooth g := smooth_of_isOpenCoverMap hg
  have : Nonempty ↥(∐ V : Scheme.{u}) := ⟨(hgs.surj (Classical.arbitrary d.X)).choose⟩
  -- the glued hypersurface `H ⊇ Y^*`
  obtain ⟨H', hH', hH'le⟩ := exists_isSmoothHypersurface_sigma V (g ≫ d.sX) (J.comap g)
    (fun i => H (e i).1)
    (fun i => by
      have h1 : Sigma.ι V i ≫ g ≫ d.sX = (U (e i).1).1.ι ≫ d.sX := by
        rw [← Category.assoc, Sigma.ι_desc]
      rw [h1]; exact hH _)
    (fun i => by
      rw [← Scheme.IdealSheafData.comap_comp, Sigma.ι_desc]; exact hHle _)
  -- `Y^* = Y ×_X X^*`
  let gY := pullback.fst d.j g
  let js := pullback.snd d.j g
  have sq : IsPullback gY js d.j g := IsPullback.of_hasPullback d.j g
  have : IsClosedImmersion js := MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq ‹_›
  have hgY : IsOpenCoverMap gY := isOpenCoverMap_of_isPullback sq.flip hg
  have hgYs : Surjective gY := MorphismProperty.of_isPullback (P := @Surjective) sq.flip hgs
  have hgYm : Smooth gY := smooth_of_isOpenCoverMap hgY
  have : Nonempty ↥(pullback d.j g : Scheme.{u}) := ⟨(hgYs.surj (Classical.arbitrary d.Y)).choose⟩
  have hker : js.ker = J.comap g := Kollar.ker_eq_comap_of_isPullback sq.flip
  let j' : pullback d.j g ⟶ H'.subscheme :=
    js.toImage ≫ Scheme.IdealSheafData.inclusion (hH'le.trans hker.symm.le)
  have hj' : j' ≫ H'.subschemeι = js := by
    simp only [j', Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    exact Scheme.Hom.toImage_imageι js
  have : IsClosedImmersion j' := by
    have : IsClosedImmersion (j' ≫ H'.subschemeι) := by rw [hj']; infer_instance
    exact IsClosedImmersion.of_comp j' H'.subschemeι
  have : Nonempty H'.subscheme := ⟨j' (Classical.arbitrary _)⟩
  -- the triples on `X^*` and `Y^*`
  have hXst : d.ambientTriple.pullback g ∈ triples :=
    pullback_mem_triples_of_isOpenCoverMap _ hXt g hg
  have hYst : d.embeddedTriple.pullback gY ∈ triples :=
    pullback_mem_triples_of_isOpenCoverMap _ hY gY hgY
  have hdXs : topologicalKrullDim ↥(∐ V : Scheme.{u}) = ((n : ℕ∞) : WithBot ℕ∞) := by
    obtain ⟨n', hn', h'⟩ := hasDimensionIn_of_isOpenCoverMap (Y := (∐ V : Scheme.{u})) _ hXt
      ⟨n, rfl, hnX⟩ g hg
    rw [h', hn']
  obtain ⟨hHe, hHd⟩ := @equidimensional_and_topologicalKrullDim_of_isSmoothHypersurface n
    (d.ambientTriple.pullback g) hXst hdXs H' hH' ‹Nonempty H'.subscheme›
  -- the closed-embedding data `Y^* ⊆ H`
  let d' : ClosedEmbeddingData.{u} :=
    { k := d.k, X := H'.subscheme, sX := H'.subschemeι ≫ g ≫ d.sX, Y := pullback d.j g,
      j := j', isClosedImmersion := inferInstance, IX := (d.IY.comap gY).map j',
      IY := d.IY.comap gY, E := OrderedDivisor.empty _, IX_eq := rfl }
  have hd'Y : d'.embeddedTriple = d.embeddedTriple.pullback gY := by
    change FieldBlowupTriple.mk ⟨pullback d.j g, d.IY.comap gY,
        (OrderedDivisor.empty H'.subscheme).comap j'⟩ d.k (j' ≫ H'.subschemeι ≫ g ≫ d.sX) =
      FieldBlowupTriple.mk ⟨pullback d.j g, d.IY.comap gY, (d.E.comap d.j).comap gY⟩ d.k
        (gY ≫ d.j ≫ d.sX)
    rw [eq_empty_of_s_eq_zero (E := (d.E.comap d.j).comap gY) hE,
      eq_empty_of_s_eq_zero (E := (OrderedDivisor.empty H'.subscheme).comap j') rfl,
      ← Category.assoc j', hj', ← Category.assoc, ← sq.w, Category.assoc]
  have hY' : d'.embeddedTriple ∈ triples := hd'Y ▸ hYst
  have hXf' : LocallyOfFiniteType d'.sX := by
    have := hXst.2.2.1
    change LocallyOfFiniteType (H'.subschemeι ≫ g ≫ d.sX)
    infer_instance
  have hXq' : QuasiCompact d'.sX := by
    have := hXst.2.2.2.1
    change QuasiCompact (H'.subschemeι ≫ g ≫ d.sX)
    infer_instance
  have hdH : dimNat d'.X = n - 1 := dimNat_eq hHd
  have P1 := ih d' (by rw [hdH, dimNat_eq hnX]; omega) rfl hY' hH'.1 hXf' hXq' hHe
  -- the hypersurface step `H ⊆ X^*` (Kollár Thm. 3.103 (3))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hI : (d.ambientTriple.pullback g).I = d'.IX.map H'.subschemeι := by
    change d.IX.comap g = ((d.IY.comap gY).map j').map H'.subschemeι
    rw [← Scheme.IdealSheafData.map_comp, hj', d.IX_eq, comap_map_of_isPullback sq]
  have hmax : maxOrder (d.ambientTriple.pullback g).I = 1 := by
    refine le_antisymm (maxOrder_le_one_of_isSmoothHypersurface hXst hH' hI) ?_
    change 1 ≤ maxOrder (d.IX.comap g)
    rw [maxOrder_comap_of_isOpenCoverMap hg hgs]
    by_contra hlt
    rw [not_le, ENat.lt_one_iff_eq_zero] at hlt
    exact hIX (eq_top_of_maxOrder_eq_zero hlt)
  have hBO := boFunctor_eq_pushforward_of_eq_map (bmoFamilyOf (boFamilyUpTo m) m) (n := m + 1)
    (by omega) (isMarkedOrderReductionFamily_bmoFamilyOf m) (d.ambientTriple.pullback g) hXst hE
    hdXs (H := H') hH' ‹Nonempty H'.subscheme› d'.IX
    (isNonzeroAtGenericPoints_map j' hYst.2.2.2.2.2.1) hI
  have hBMO := bmoFamily_eq_boFamily_of_maxOrder_eq (n := m + 1) (m := 1)
    (d.ambientTriple.pullback g) hXst (eq_empty_of_s_eq_zero hE) hdXs (by exact_mod_cast hmax)
    le_rfl
  have P2 : ClosedBlowupSequence.IsPushforward H'.subschemeι
      (bmoFamily (dimNat d'.X) 1 ⟨d'.ambientTriple, 1⟩)
      (bmoFamily (m + 1) 1 ⟨d.ambientTriple.pullback g, 1⟩) := by
    refine isPushforward_congr_right (hBMO.trans ((boFamily_succ m _).trans hBO)) ?_
    refine isPushforward_congr_left ?_ (isPushforward_pushforward H'.subschemeι _)
    rw [hdH]
    exact (bmoFamilyOf_eq le_rfl 1 _).symm
  have P12 := isPushforward_comp _ j' H'.subschemeι _ _ P1 P2
  rw [hj'] at P12
  -- descent along `X^* → X`
  have : Flat g := inferInstance
  refine isPushforward_of_pullback _ _ sq ?_
  have e1 : (bmoFamily (dimNat d.Y) 1 ⟨d.embeddedTriple, 1⟩).pullback gY =
      bmoFamily (dimNat d'.Y) 1 ⟨d'.embeddedTriple, 1⟩ :=
    (bmoFamily_pullback_of_surjective hY gY hgYm hgYs hYst).symm.trans
      (eq_of_heq (bmoFamily_congr (by rw [hd'Y])))
  have e2 : (bmoFamily (dimNat d.X) 1 ⟨d.ambientTriple, 1⟩).pullback g =
      bmoFamily (m + 1) 1 ⟨d.ambientTriple.pullback g, 1⟩ :=
    (bmoFamily_pullback_of_surjective hXt g (smooth_of_isOpenCoverMap hg) hgs hXst).symm.trans
      (by rw [dimNat_eq hdXs])
  exact isPushforward_congr_left e1 (isPushforward_congr_right e2 P12)

end Positive

/-- `isPushforward_bmoFamily_of_closedEmbedding` for closed-embedding data whose ambient scheme
has dimension index `n`. -/
private theorem isPushforward_bmoFamily_of_dimNat_eq (n : ℕ) :
    ∀ d : ClosedEmbeddingData.{u}, dimNat d.X = n → d.E.s = 0 →
    d.embeddedTriple ∈ triples → MMP.Mori.IsSmoothScheme d.sX →
    LocallyOfFiniteType d.sX → QuasiCompact d.sX → Equidimensional d.X →
    ClosedBlowupSequence.IsPushforward d.j
      (bmoFamily (dimNat d.Y) 1 ⟨d.embeddedTriple, 1⟩)
      (bmoFamily (dimNat d.X) 1 ⟨d.ambientTriple, 1⟩) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro d hn hE hY hXs hXf hXq hXe
    by_cases hYe : IsEmpty d.Y
    · exact isPushforward_of_isEmpty d hE hY hXs hXf hXq hXe
    rw [not_isEmpty_iff] at hYe
    by_cases hc : dimNat d.X = dimNat d.Y
    · exact isPushforward_of_dimNat_eq d hE hY hXs hXf hXq hXe hc
    · exact isPushforward_of_dimNat_ne d hE hY hXs hXf hXq hXe hc
        fun d' hd' => ih (dimNat d'.X) (hn ▸ hd') d' rfl

/-- **Kollár, Claim 3.71.2 (proof 3.108).** Let `d` be closed-embedding data `τ : Y ↪ X` over a
field `k` of characteristic `0` with `E = ∅` and `I_X = τ_* I_Y` (i.e. `𝒪_X/I_X = τ_*(𝒪_Y/I_Y)`),
such that `(Y, I_Y, ∅)` is a triple (`Y` smooth, equidimensional, of finite type over `k`, `I_Y`
nonzero at the generic point of every irreducible component) and `X` is smooth, equidimensional
and of finite type over `k`. Then `bmoFamily (dimNat X) 1 (X, I_X, 1, ∅)` is the push-forward
along `τ` of `bmoFamily (dimNat Y) 1 (Y, I_Y, 1, ∅)`. -/
@[mmp "thm_kr3e_bmo_closed_embedding"]
public theorem isPushforward_bmoFamily_of_closedEmbedding (d : ClosedEmbeddingData.{u})
    (hE : d.E.s = 0) (hY : d.embeddedTriple ∈ triples)
    (hXs : MMP.Mori.IsSmoothScheme d.sX) (hXf : LocallyOfFiniteType d.sX)
    (hXq : QuasiCompact d.sX) (hXe : Equidimensional d.X) :
    ClosedBlowupSequence.IsPushforward d.j
      (bmoFamily (dimNat d.Y) 1 ⟨d.embeddedTriple, 1⟩)
      (bmoFamily (dimNat d.X) 1 ⟨d.ambientTriple, 1⟩) :=
  isPushforward_bmoFamily_of_dimNat_eq _ d rfl hE hY hXs hXf hXq hXe

/-- **The canonical `𝓑𝓜𝓞_1` has the closed embedding property.** The assignment
`t ↦ bmoFamily (dimNat t.X) 1 t` on the marked triples of marking `1`
(`markedTriplesOfMarking 1`) satisfies `HasClosedEmbeddingProperty`: along a closed embedding
`τ : Y ↪ X` with `τ_*(𝒪_Y/J) = 𝒪_X/I` and empty divisor, the sequence assigned to
`(X, I, 1, ∅)` is the pushforward along `τ` of the one assigned to `(Y, J, 1, ∅)`. -/
@[mmp "thm_kr3e_bmo_closed_embedding_property"]
public theorem hasClosedEmbeddingProperty_bmoFamily :
    HasClosedEmbeddingProperty.{u} (fun t _ => bmoFamily (dimNat t.X) 1 t) := by
  intro d hE hX hY
  obtain ⟨_, hXs, hXf, hXq, hXe, _, _⟩ := hX.1
  exact isPushforward_bmoFamily_of_closedEmbedding d hE hY.1 hXs hXf hXq hXe

end MMP.Resolution
