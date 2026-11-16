module

public import StacksFrontier.Order.HeightCoheight
public import MMP.RingTheory.KrullDimension.HeightAddCoheight
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# Height plus coheight on schemes of finite type over a field

On an integral scheme `X` locally of finite type over a field `K`, ordered by `y ≤ x ↔ x ⤳ y`,
every point `x` satisfies `height x + coheight x = dim X`: the dimension of the closure of `x` plus
its codimension is the dimension of `X`.

This is the catenarity and equidimensionality of finite type domains over a field (Stacks 00OS:
every maximal chain of primes of such a domain `A` has length `dim A`,
`Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim`), transported
to `X`:

* for a prime `p` of `A`, splicing a longest chain of primes ending at `p` with a longest chain
  starting at `p` gives a maximal chain, so `dim A ≤ height p + coheight p`;
* for an affine open `U = Spec A` of `X`, the inclusion `U → X` reverses the order of primes
  strictly, so `height p + coheight p ≤ height x + coheight x` for the point `x` of `p`;
* the coheight of a closed point `w ∈ U` is the height of its maximal ideal, which is `dim A`;
  since `X` is irreducible and Jacobson, two nonempty affine opens share a closed point, so all
  closed points of `X` have the same coheight `d`, and `dim X ≤ d` because every chain of points
  of `X` lies above a closed point.

## Main results

* `MMP.height_add_coheight_eq_krullDim`: for an integral scheme `X` locally of finite type over a
  field, every point `x` satisfies `height x + coheight x = dim X`.
* `MMP.krullDim_lt_top_of_isIntegral`, `MMP.coheight_lt_top_of_locallyOfFiniteType`: such a scheme
  is finite-dimensional, and every point has finite coheight.
* `MMP.height_eq_height_add_coheight_Iic`: catenarity along the closure of a point.

The ring case, `dim A ≤ height p + coheight p` for a prime `p` of a finite type domain `A`, is
`MMP.ringKrullDim_le_height_add_coheight` (`MMP/RingTheory/KrullDimension/HeightAddCoheight`).

## References

* [Stacks Project, Tag 00OS](https://stacks.math.columbia.edu/tag/00OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order Topology

universe u

namespace MMP

/-! ### Affine opens -/

/-- The sections over an affine open of a scheme locally of finite type over `K` form a `K`-algebra
of finite type, through the structure morphism. -/
theorem exists_ringHom_finiteType_of_isAffineOpen {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))] {U : X.Opens}
    (hU : IsAffineOpen U) : ∃ φ : K →+* Γ(X, U), φ.FiniteType := by
  refine ⟨((X ↘ Spec (.of K)).appLE ⊤ U (by simp)).hom.comp
    (Scheme.ΓSpecIso (.of K)).inv.hom, ?_⟩
  refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _ ?_)
  · exact HasRingHomProperty.appLE @LocallyOfFiniteType (X ↘ Spec (.of K)) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  · exact (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective

/-- The coheight of a point `x` of an affine open `U` (the supremum of the lengths of chains of
generizations of `x`) is the height of the prime ideal of `Γ(X, U)` corresponding to `x`. -/
theorem coheight_eq_height_primeIdealOf {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : U) : coheight (x : X) = (hU.primeIdealOf x).asIdeal.height := by
  have := hU.isLocalization_stalk x
  have h₂ := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf x).asIdeal
    (X.presheaf.stalk (x : X))
  rw [ringKrullDim_stalk_eq_coheight] at h₂
  exact_mod_cast h₂

/-- The open immersion `Spec Γ(X, U) → X` of an affine open reverses the order strictly: an
inclusion of primes `p ⊊ q` is a strict specialization `p ⤳ q`. -/
theorem strictAnti_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    StrictAnti (fun p : PrimeSpectrum Γ(X, U) ↦ hU.fromSpec p) := by
  intro p q hpq
  refine lt_of_le_not_ge ?_ ?_
  · rw [Scheme.le_iff_specializes]
    exact ((PrimeSpectrum.le_iff_specializes p q).mp hpq.le).map hU.fromSpec.continuous
  · rw [Scheme.le_iff_specializes]
    intro h
    exact hpq.not_ge ((PrimeSpectrum.le_iff_specializes q p).mpr
      (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp h))

/-- A closed point of `X` in an affine open `U` corresponds to a maximal ideal of `Γ(X, U)`. -/
theorem isMaximal_primeIdealOf_of_isClosed {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : U) (hx : IsClosed {(x : X)}) : (hU.primeIdealOf x).asIdeal.IsMaximal := by
  rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  have : ({hU.primeIdealOf x} : Set (PrimeSpectrum Γ(X, U))) = hU.fromSpec ⁻¹' {(x : X)} := by
    ext q
    simp only [Set.mem_singleton_iff]
    rw [← hU.fromSpec_primeIdealOf x]
    exact hU.fromSpec.isOpenEmbedding.injective.eq_iff.symm
  rw [this]
  exact hx.preimage hU.fromSpec.continuous

/-- The closure of a point of a scheme has dimension the height of the point. -/
theorem topologicalKrullDim_closure_singleton_eq_height {X : Scheme.{u}} (x : X) :
    topologicalKrullDim (closure {x} : Set X) = height x := by
  let T : Set X := closure {x}
  have hTc : IsClosed T := isClosed_closure
  have : QuasiSober T := hTc.isClosedEmbedding_subtypeVal.quasiSober
  have hpre : (specializationOrder T).toPreorder = (inferInstance : Preorder T) :=
    Preorder.ext fun a b => (Topology.IsInducing.subtypeVal.specializes_iff (x := b) (y := a)).symm
  have hheight : ∀ a : T, height a = height (a : X) := by
    refine height_eq_of_strictMono _ (Subtype.strictMono_coe _) fun a b hb => ?_
    have hbT : b ∈ T := (Scheme.le_iff_specializes.mp hb.le).mem_closed hTc a.2
    exact ⟨⟨b, hbT⟩, hb, rfl⟩
  have hx : x ∈ T := subset_closure rfl
  change krullDim (TopologicalSpace.IrreducibleCloseds T) = _
  rw [@Order.krullDim_eq_of_orderIso _ _ _ (specializationOrder T).toPreorder
    irreducibleSetEquivPoints, hpre,
    krullDim_eq_iSup_height]
  refine le_antisymm (iSup_le fun a => ?_) (le_iSup_of_le ⟨x, hx⟩ ?_)
  · rw [hheight a]
    exact WithBot.coe_le_coe.mpr (height_mono (Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr a.2)))
  · rw [hheight ⟨x, hx⟩]

/-- In a Jacobson scheme every point specializes to a closed point. -/
theorem exists_le_isClosed_singleton {X : Scheme.{u}} [JacobsonSpace X] (y : X) :
    ∃ z, z ≤ y ∧ IsClosed {z} := by
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (⟨y, subset_closure rfl⟩ : (closure {y}).Nonempty) isClosed_closure.isLocallyClosed
  exact ⟨z, Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hz), hzc⟩

/-! ### Integral schemes locally of finite type over a field -/

section LocallyOfFiniteType

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (.of K))]

include K in
/-- On an integral scheme locally of finite type over a field, the coheight of a closed point `w`
of a nonempty affine open `U` is the Krull dimension of `Γ(X, U)`. -/
theorem coheight_eq_ringKrullDim_of_isClosed {U : X.Opens} (hU : IsAffineOpen U) (w : U)
    (hw : IsClosed {(w : X)}) : (coheight (w : X) : WithBot ℕ∞) = ringKrullDim Γ(X, U) := by
  obtain ⟨φ, hφ⟩ := exists_ringHom_finiteType_of_isAffineOpen (K := K) hU
  let := φ.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := hφ
  have : Nonempty U := ⟨w⟩
  have := isMaximal_primeIdealOf_of_isClosed hU w hw
  rw [coheight_eq_height_primeIdealOf hU w,
    (Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim K
      Γ(X, U)).1 (hU.primeIdealOf w).asIdeal]

include K in
/-- On an integral scheme locally of finite type over a field, all closed points have the same
coheight. -/
theorem coheight_eq_coheight_of_isClosed {w w' : X} (hw : IsClosed {w}) (hw' : IsClosed {w'}) :
    coheight w = coheight w' := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of K))
  obtain ⟨U, hU, hwU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show w ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨U', hU', hwU', -⟩ :=
    exists_isAffineOpen_mem_and_subset (show w' ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨v, hv, hvc⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter U.isOpen U'.isOpen ⟨w, hwU⟩ ⟨w', hwU'⟩)
    (U.isOpen.inter U'.isOpen).isLocallyClosed
  have h₁ := coheight_eq_ringKrullDim_of_isClosed K hU ⟨w, hwU⟩ hw
  have h₂ := coheight_eq_ringKrullDim_of_isClosed K hU ⟨v, hv.1⟩ hvc
  have h₃ := coheight_eq_ringKrullDim_of_isClosed K hU' ⟨v, hv.2⟩ hvc
  have h₄ := coheight_eq_ringKrullDim_of_isClosed K hU' ⟨w', hwU'⟩ hw'
  exact_mod_cast h₁.trans (h₂.symm.trans (h₃.trans h₄.symm))

include K in
/-- On an integral scheme locally of finite type over a field, the dimension is bounded by the
coheight of any closed point. -/
theorem krullDim_le_coheight_of_isClosed {z : X} (hz : IsClosed {z}) :
    krullDim X ≤ coheight z := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of K))
  refine iSup_le fun q ↦ ?_
  obtain ⟨w, hwq, hwc⟩ := exists_le_isClosed_singleton q.head
  have h₁ : (q.length : ℕ∞) ≤ coheight w := length_le_coheight_head.trans (coheight_anti hwq)
  rw [coheight_eq_coheight_of_isClosed K hwc hz] at h₁
  exact_mod_cast h₁

include K in
/-- On an integral scheme `X` locally of finite type over a field, every point `x` satisfies
`height x + coheight x = dim X`, for the order `y ≤ x ↔ x ⤳ y`: the dimension of the closure of
`x` plus the codimension of the closure of `x` is the dimension of `X`. -/
theorem height_add_coheight_eq_krullDim (x : X) :
    ((height x + coheight x : ℕ∞) : WithBot ℕ∞) = krullDim X := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of K))
  refine le_antisymm (by exact_mod_cast Order.height_add_coheight_le_krullDim x) ?_
  obtain ⟨z, hzx, hzc⟩ := exists_le_isClosed_singleton x
  obtain ⟨U, hU, hzU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : X.Opens) from trivial)
  have hxU : x ∈ U := (Scheme.le_iff_specializes.mp hzx).mem_open U.isOpen hzU
  obtain ⟨φ, hφ⟩ := exists_ringHom_finiteType_of_isAffineOpen (K := K) hU
  let := φ.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := hφ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  set p := hU.primeIdealOf ⟨x, hxU⟩
  have hpx : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hmono : StrictMono
      (fun q : (PrimeSpectrum Γ(X, U))ᵒᵈ ↦ hU.fromSpec (OrderDual.ofDual q)) :=
    fun a b h ↦ strictAnti_fromSpec hU h
  have e₁ : coheight p ≤ height x := by
    have := height_le_height_apply_of_strictMono _ hmono (OrderDual.toDual p)
    rw [height_toDual] at this
    refine this.trans_eq ?_
    rw [← hpx]
    rfl
  have e₂ : height p ≤ coheight x := by
    have := coheight_le_coheight_apply_of_strictMono _ hmono (OrderDual.toDual p)
    rw [coheight_toDual] at this
    refine this.trans_eq ?_
    rw [← hpx]
    rfl
  calc krullDim X ≤ coheight z := krullDim_le_coheight_of_isClosed K hzc
    _ = ringKrullDim Γ(X, U) := coheight_eq_ringKrullDim_of_isClosed K hU ⟨z, hzU⟩ hzc
    _ ≤ ((height p + coheight p : ℕ∞) : WithBot ℕ∞) :=
      ringKrullDim_le_height_add_coheight K Γ(X, U) p
    _ ≤ ((height x + coheight x : ℕ∞) : WithBot ℕ∞) := by
      rw [add_comm (height p)]
      exact_mod_cast add_le_add e₁ e₂

end LocallyOfFiniteType

/-! ### Heights in intervals and finiteness -/

/-- The height of an element of `Set.Iic b` is its height in the ambient preorder. -/
theorem height_coe_Iic {α : Type*} [Preorder α] {b : α} (a : Set.Iic b) :
    height a = height (a : α) := by
  refine le_antisymm
    (height_le_height_apply_of_strictMono (Subtype.val : Set.Iic b → α) (fun _ _ h ↦ h) a) ?_
  refine height_le fun p hp ↦ ?_
  let q : LTSeries (Set.Iic b) :=
    ⟨p.length, fun i ↦ ⟨p i, ((p.monotone (Fin.le_last i)).trans hp.le).trans a.2⟩,
      fun i ↦ p.step i⟩
  exact length_le_height (p := q) (show q.last ≤ a from hp.le)

/-- If the last element of an `LTSeries` `p` is at most `b`, then `p.length` bounds the coheight
of `p.head` in `Set.Iic b`. -/
theorem length_le_coheight_Iic {α : Type*} [Preorder α] {b : α} (p : LTSeries α)
    (hb : p.last ≤ b) : (p.length : ℕ∞) ≤
      coheight (⟨p.head, (p.monotone (Fin.zero_le _)).trans hb⟩ : Set.Iic b) := by
  let q : LTSeries (Set.Iic b) :=
    ⟨p.length, fun i ↦ ⟨p i, (p.monotone (Fin.le_last i)).trans hb⟩, fun i ↦ p.step i⟩
  exact length_le_coheight (p := q) le_rfl

/-- A closed point of a scheme is minimal for the order `y ≤ z ↔ z ⤳ y`, so its height is zero. -/
theorem height_eq_zero_of_isClosed {X : Scheme.{u}} {z : X} (hz : IsClosed {z}) :
    height z = 0 :=
  Scheme.height_of_isClosed hz

/-- An integral scheme locally of finite type over a field is finite-dimensional. -/
theorem krullDim_lt_top_of_isIntegral (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of K))] :
    krullDim X < ⊤ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of K))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := X))
    isClosed_univ.isLocallyClosed
  rw [← height_add_coheight_eq_krullDim K z, height_eq_zero_of_isClosed hz, zero_add,
    ← ringKrullDim_stalk_eq_coheight]
  exact ringKrullDim_lt_top

/-- On a scheme locally of finite type over a field, every point has finite coheight: it is the
dimension of the Noetherian local ring at the point. -/
theorem coheight_lt_top_of_locallyOfFiniteType (K : Type u) [Field K] {Y : Scheme.{u}}
    [Y.Over (Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))] (x : Y) :
    coheight x < ⊤ := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  have h : ((coheight x : ℕ∞) : WithBot ℕ∞) < ⊤ := by
    rw [← ringKrullDim_stalk_eq_coheight]
    exact ringKrullDim_lt_top
  rwa [← WithBot.coe_top, WithBot.coe_lt_coe] at h

/-- The closed immersion of the reduced closed subscheme on `closure {η}` identifies its points,
ordered by `y ≤ z ↔ z ⤳ y`, with the interval `Set.Iic η` of `Y`. -/
def integralComponentAtOrderIsoIic {Y : Scheme.{u}} (η : Y) :
    (Stacks.Chow.integralComponentAt η).subscheme ≃o Set.Iic η := by
  let ι := (Stacks.Chow.integralComponentAt η).subschemeι
  let f : (Stacks.Chow.integralComponentAt η).subscheme ↪o Y :=
    { toFun := ι
      inj' := ι.isEmbedding.injective
      map_rel_iff' := fun {a b} ↦ by
        change ι a ≤ ι b ↔ a ≤ b
        rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
        exact ι.isEmbedding.specializes_iff }
  have hrange : Set.range f = Set.Iic η := by
    ext y
    change y ∈ Set.range ι ↔ y ≤ η
    rw [Scheme.IdealSheafData.range_subschemeι, Stacks.Chow.coe_support_integralComponentAt,
      Scheme.le_iff_specializes, specializes_iff_mem_closure]
  exact f.orderIso.trans (Set.orderIsoOfEq _ _ hrange)

/-- **Catenarity along an irreducible closed subset.** On a scheme locally of finite type over a
field, for points `x ≤ η` (`η ⤳ x`), `height η = height x + c` where `c` is the coheight of `x` in
`Set.Iic η`, and all three are finite. -/
theorem height_eq_height_add_coheight_Iic (K : Type u) [Field K] {Y : Scheme.{u}}
    [Y.Over (Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))] {x η : Y} (hx : x ≤ η) :
    height η = height x + coheight (⟨x, hx⟩ : Set.Iic η) ∧ height η < ⊤ := by
  let W := Stacks.Chow.integralComponentAt η
  have : IsIntegral W.subscheme := Stacks.Chow.isIntegral_integralComponentAt η
  let : W.subscheme.Over (Spec (.of K)) := ⟨W.subschemeι ≫ (Y ↘ Spec (.of K))⟩
  have : LocallyOfFiniteType (W.subscheme ↘ Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (W.subschemeι ≫ (Y ↘ Spec (.of K))))
  let e := integralComponentAtOrderIsoIic η
  have hdim : krullDim W.subscheme = height η := by
    rw [krullDim_eq_of_orderIso e, height_eq_krullDim_Iic]
  have key := height_add_coheight_eq_krullDim K (e.symm ⟨x, hx⟩)
  rw [← height_orderIso e, ← coheight_orderIso e, e.apply_symm_apply, height_coe_Iic, hdim] at key
  refine ⟨(WithBot.coe_inj.mp key).symm, ?_⟩
  have := krullDim_lt_top_of_isIntegral K W.subscheme
  rwa [hdim, ← WithBot.coe_top, WithBot.coe_lt_coe] at this

end MMP
