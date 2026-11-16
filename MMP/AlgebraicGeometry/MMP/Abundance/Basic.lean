/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import MMP.AlgebraicGeometry.Intersection.Nef
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularSmooth
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationDimensionOne
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.NonFlatLocusFibreDimension
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisorStalk
public import StacksFrontier.AlgebraicGeometry.FunctionField.GenericPointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.FreeSectionsAffineNeighborhood
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.MapDomain
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjToSpecZero
public import StacksFrontier.AlgebraicGeometry.Perfect.InvertibleFibreEulerConstant
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.DominantClosure
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.StalkLengthGenericPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.GenericFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorization

/-!
# Lemmas for the definitions of `MMP.Foundations.Flips.Abundance`

The facts the source text of three definitions of `MMP.Foundations.Flips.Abundance` asserts in
passing, in the generality in which they are proved.

* The generic fibre `V_η` of a surjective morphism `g : V ⟶ W` of varieties with
  `dim V = dim W + 1` (FA 15.1.1): its points are the points of `V` over the generic point `η`
  of `W`, with the local rings of `V`; it has dimension one
  (`MMP.Flips.topologicalKrullDim_genericFiber_eq_one`), is proper over `κ(η)` when `g` is
  (`MMP.Flips.isProper_fiberToSpecResidueField`), its local rings are regular when `V` is normal
  (`MMP.Flips.isRegularLocalRing_stalk_of_mem_genericFiber`), and a prime divisor meets it at most
  in its generic point, a closed point of `V_η`
  (`MMP.Flips.eq_genericPoint_of_mem_support_of_mem_genericFiber`,
  `MMP.Flips.isClosed_singleton_genericFiber`).
* The normalization of a scheme of pure dimension one, locally of finite type over a perfect
  field, is smooth (`MMP.Flips.smooth_normalization_comp_of_dim_le_one`; FA 12.2.9).
* An `ℝ`-Cartier `ℚ`-divisor is `ℚ`-Cartier
  (`MMP.Flips.QDivisor.isQCartier_of_isCartierCombination`) and a small birational contraction
  is birational (`MMP.Flips.IsSmall.isBirationalMorphism`; FA 15.4.4, 15.9).

## Implementation notes

The module also re-exports the Stacks project results on which the Chow variety of curve cycles
of fixed degree on a projective scheme (FA 15) rests: the points of `Proj` over its degree-zero
part, flatness over a Dedekind scheme of an integral scheme dominating it, finiteness of stalk
lengths exactly at generic points, constancy of fibre Euler characteristics of invertible sheaves
in a proper flat family, generic flatness and Stein factorization.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 12.2.9, 15.1.1,
  15.4.4, 15.9
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Flips

/-- A space whose irreducible components all have dimension at most `n` has dimension at most
`n`. -/
theorem topologicalKrullDim_le_of_forall_mem_irreducibleComponents {X : Type*}
    [TopologicalSpace X] {n : WithBot ℕ∞}
    (h : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z ≤ n) :
    topologicalKrullDim X ≤ n := by
  unfold topologicalKrullDim
  rw [Order.krullDim, iSup_le_iff]
  intro p
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (p.last : Set X) p.last.isIrreducible
  have hle : ∀ i, (p i : Set X) ⊆ W := fun i =>
    (show (p i : Set X) ⊆ (p.last : Set X) from p.monotone (Fin.le_last i)).trans hsub
  let f : Fin (p.length + 1) → IrreducibleCloseds W := fun i =>
    { carrier := Subtype.val ⁻¹' (p i : Set X)
      isIrreducible' := by
        have := Subtype.irreducibleSpace (p i).isIrreducible
        have hc : Continuous (fun s : (p i : Set X) => (⟨s.1, hle i s.2⟩ : W)) := by fun_prop
        have := (IrreducibleSpace.isIrreducible_univ (p i : Set X)).image _ hc.continuousOn
        convert this using 1
        ext ⟨x, hx⟩
        simp
      isClosed' := (p i).isClosed.preimage continuous_subtype_val }
  have hf : StrictMono f := by
    intro i j hij
    refine lt_of_le_of_ne (fun x hx => (show (p i : Set X) ⊆ p j from p.monotone hij.le) hx) ?_
    intro heq
    apply (p.strictMono hij).ne
    ext x
    constructor
    · intro hx
      have : (⟨x, hle i hx⟩ : W) ∈ (f i : Set W) := hx
      rwa [heq] at this
    · intro hx
      have : (⟨x, hle j hx⟩ : W) ∈ (f j : Set W) := hx
      rwa [← heq] at this
  let q : LTSeries (IrreducibleCloseds W) :=
    ⟨p.length, f, fun i => hf (Fin.castSucc_lt_succ (i := i))⟩
  exact (Order.LTSeries.length_le_krullDim q).trans (h W hW)

/-- Three distinct points `a ⤳ b ⤳ c` of a subset `S` of a `T₀` space give `dim S ≥ 2`. -/
theorem two_le_topologicalKrullDim_of_specializes {X : Type*} [TopologicalSpace X] [T0Space X]
    {S : Set X} {a b c : X} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ⤳ b) (hbc : b ⤳ c)
    (hab' : a ≠ b) (hbc' : b ≠ c) : 2 ≤ topologicalKrullDim S := by
  let cl : S → IrreducibleCloseds S := fun x =>
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : ∀ x y : S, x ⤳ y → x ≠ y → cl y < cl x := by
    intro x y hxy hne
    refine lt_of_le_of_ne ?_ ?_
    · change closure {y} ⊆ closure {x}
      exact hxy.closure_subset
    · intro heq
      have h2 : x ∈ closure ({y} : Set S) := by
        have : x ∈ (cl x : Set S) := subset_closure rfl
        rwa [← heq] at this
      exact hne (hxy.antisymm (specializes_iff_mem_closure.mpr h2)).eq
  have h1 := hlt ⟨b, hb⟩ ⟨c, hc⟩ ((subtype_specializes_iff _ _).mpr hbc) (by simpa using hbc')
  have h2 := hlt ⟨a, ha⟩ ⟨b, hb⟩ ((subtype_specializes_iff _ _).mpr hab) (by simpa using hab')
  let q : LTSeries (IrreducibleCloseds S) :=
    ⟨2, ![cl ⟨c, hc⟩, cl ⟨b, hb⟩, cl ⟨a, ha⟩], by
      intro i
      fin_cases i
      · exact h1
      · exact h2⟩
  exact_mod_cast Order.LTSeries.length_le_krullDim q

end MMP.Flips

namespace MMP.Flips

variable {k : Type u} [Field k] {V W : Scheme.{u}} (sV : V ⟶ Spec (.of k))
  (sW : W ⟶ Spec (.of k)) (g : V ⟶ W)

/-- For a morphism `g : V ⟶ W` of `k`-schemes and a point `x : V`, the transcendence degree of
`κ(x)` over `k` is the sum of those of `κ(g x)` over `k` and of `κ(x)` over `κ(g x)`. -/
theorem trdeg_residueField_add (hg : g ≫ sW = sV) (x : V) :
    letI : Algebra k (V.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sV.appTop ≫ V.Γevaluation x).hom.toAlgebra
    letI : Algebra k (W.residueField (g x)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sW.appTop ≫ W.Γevaluation (g x)).hom.toAlgebra
    letI : Algebra (W.residueField (g x)) (V.residueField x) := (g.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg k (W.residueField (g x)) +
        Algebra.trdeg (W.residueField (g x)) (V.residueField x) =
      Algebra.trdeg k (V.residueField x) := by
  let : Algebra k (V.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sV.appTop ≫ V.Γevaluation x).hom.toAlgebra
  let : Algebra k (W.residueField (g x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sW.appTop ≫ W.Γevaluation (g x)).hom.toAlgebra
  let : Algebra (W.residueField (g x)) (V.residueField x) := (g.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower k (W.residueField (g x)) (V.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ sV.appTop ≫ V.Γevaluation x).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sW.appTop ≫ W.Γevaluation (g x) ≫
        g.residueFieldMap x).hom
    rw [Scheme.Γevaluation_naturality, ← hg, Scheme.Hom.comp_appTop]
    simp only [Category.assoc]
  have : FaithfulSMul k (W.residueField (g x)) :=
    (faithfulSMul_iff_algebraMap_injective ..).mpr (algebraMap k (W.residueField (g x))).injective
  have : FaithfulSMul (W.residueField (g x)) (V.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective ..).mpr
      (algebraMap (W.residueField (g x)) (V.residueField x)).injective
  exact trdeg_add_eq k (W.residueField (g x))

variable [IsIntegral W]

/-- A point of `V` generalizing a point of the generic fibre lies in the generic fibre. -/
theorem mem_genericFiber_of_specializes {x y : V} (hyx : y ⤳ x) (hx : g x = genericPoint W) :
    g y = genericPoint W := by
  have h : g y ⤳ genericPoint W := hx ▸ hyx.map g.continuous
  have hgen : IsGenericPoint (g y) (Set.univ : Set W) := by
    rw [IsGenericPoint]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec W).def]
    exact h.closure_subset
  exact hgen.eq (genericPoint_spec W)

variable [IsIntegral V]

/-- A surjective morphism of integral schemes maps the generic point to the generic point. -/
theorem genericPoint_map_of_surjective (hs : Function.Surjective g) :
    g (genericPoint V) = genericPoint W := by
  obtain ⟨x, hx⟩ := hs (genericPoint W)
  exact mem_genericFiber_of_specializes g ((genericPoint_spec V).specializes (Set.mem_univ x)) hx

omit [IsIntegral W] [IsIntegral V] in
include sW in
/-- If `g ≫ sW = sV` with `sV` locally of finite type, then `g` is locally of finite type. -/
theorem locallyOfFiniteType_of_comp_eq [LocallyOfFiniteType sV] (hg : g ≫ sW = sV) :
    LocallyOfFiniteType g := by
  have : LocallyOfFiniteType (g ≫ sW) := hg ▸ inferInstance
  exact locallyOfFiniteType_of_comp g sW

omit [IsIntegral W] in
/-- The generic point of `V` is the generic point of the generic fibre. -/
theorem isGenericPoint_asFiber_genericPoint :
    IsGenericPoint (g.asFiber (genericPoint V))
      (Set.univ : Set (g.fiber (g (genericPoint V)))) := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.mem_univ, iff_true]
  rw [← (g.fiberι (g (genericPoint V))).isEmbedding.isInducing.specializes_iff,
    Scheme.Hom.fiberι_asFiber]
  exact (genericPoint_spec V).specializes (Set.mem_univ _)

variable [LocallyOfFiniteType sV] [LocallyOfFiniteType sW] [CompactSpace W]

/-- **The generic fibre is a curve.** If `dim V = dim W + 1`, the fibre `V_η` of `g` over the
generic point `η` of `W` has dimension one. -/
theorem topologicalKrullDim_genericFiber_eq_one (hg : g ≫ sW = sV) (hs : Function.Surjective g)
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1) :
    topologicalKrullDim (g.fiber (genericPoint W)) = 1 := by
  have := locallyOfFiniteType_of_comp_eq sV sW g hg
  have hθ := genericPoint_map_of_surjective g hs
  have dF := toENat_trdeg_eq_topologicalKrullDim_fiber g (genericPoint V)
    (isGenericPoint_asFiber_genericPoint g)
  have dV := topologicalKrullDim_eq_trdeg_residueField k V sV (genericPoint V) (genericPoint_spec V)
  have dW := topologicalKrullDim_eq_trdeg_residueField k W sW (g (genericPoint V))
    (hθ ▸ genericPoint_spec W)
  have ht := congrArg Cardinal.toENat (trdeg_residueField_add sV sW g hg (genericPoint V))
  rw [map_add] at ht
  have hWne := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sW
  rw [← hθ, ← dF]
  rw [dV, dW] at hdim
  rw [dW] at hWne
  revert hdim hWne ht
  generalize Cardinal.toENat _ = a
  generalize Cardinal.toENat _ = b
  generalize Cardinal.toENat _ = c
  intro hdim ht hWne
  have hWne' : b ≠ ⊤ := fun h => hWne (by rw [h]; rfl)
  subst ht
  have : b + c = b + 1 := by exact_mod_cast hdim
  have := (WithTop.add_left_inj (α := ℕ) hWne').mp this
  rw [this]
  rfl

/-- The local ring of `V` at a point of the generic fibre has dimension at most one. -/
theorem ringKrullDim_stalk_le_one_of_mem_genericFiber (hg : g ≫ sW = sV)
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1) {x : V}
    (hx : g x = genericPoint W) : ringKrullDim (V.presheaf.stalk x) ≤ 1 := by
  have dAt := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k V sV x
  rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k V sV x] at dAt
  have dW := topologicalKrullDim_eq_trdeg_residueField k W sW (g x) (hx ▸ genericPoint_spec W)
  have ht := congrArg Cardinal.toENat (trdeg_residueField_add sV sW g hg x)
  rw [map_add] at ht
  have hWne := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sW
  rw [dAt, dW] at hdim
  rw [dW] at hWne
  revert hdim hWne ht
  generalize Cardinal.toENat _ = a
  generalize Cardinal.toENat _ = b
  generalize Cardinal.toENat _ = c
  generalize ringKrullDim (V.presheaf.stalk x) = r
  intro hdim ht hWne
  have hWne' : b ≠ ⊤ := fun h => hWne (by rw [h]; rfl)
  subst ht
  induction r using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe r =>
    have : b + (c + r) = b + 1 := by
      rw [← add_assoc]
      exact_mod_cast hdim
    have := (WithTop.add_left_inj (α := ℕ) hWne').mp this
    have h' : c + r = (1 : ℕ∞) := this
    have h'' : r ≤ (1 : ℕ∞) := h' ▸ le_add_self
    exact_mod_cast h''

/-- **The generic fibre is regular** (FA 15.1.1): every local ring of `V` at a point of the
generic fibre (a local ring of `V_η`) is a regular local ring. -/
theorem isRegularLocalRing_stalk_of_mem_genericFiber [IsNormal V] (hg : g ≫ sW = sV)
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1) {x : V}
    (hx : g x = genericPoint W) : IsRegularLocalRing (V.presheaf.stalk x) := by
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have hd := ringKrullDim_stalk_le_one_of_mem_genericFiber sV sW g hg hdim hx
  have : IsDomain (V.presheaf.stalk x) := IsNormal.stalk_isDomain x
  have : IsIntegrallyClosed (V.presheaf.stalk x) := IsNormal.stalk_normal x
  have : Ring.KrullDimLE 1 (V.presheaf.stalk x) := Ring.krullDimLE_iff.mpr (by exact_mod_cast hd)
  have : Ring.DimensionLEOne (V.presheaf.stalk x) := ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩
  have : IsDedekindRing (V.presheaf.stalk x) := ⟨⟩
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing _

/-- A prime divisor `E` of `V` meets the generic fibre at most in its generic point, which then
lies over `η`. -/
theorem eq_genericPoint_of_mem_support_of_mem_genericFiber (hg : g ≫ sW = sV)
    (hs : Function.Surjective g) (hdim : topologicalKrullDim V = topologicalKrullDim W + 1)
    (E : Mori.PrimeDivisor V) {x : V} (hxE : x ∈ (E.support : Set V))
    (hx : g x = genericPoint W) : x = E.genericPoint ∧ g E.genericPoint = genericPoint W := by
  have hξx : E.genericPoint ⤳ x := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
    exact specializes_iff_mem_closure.mpr hxE
  have hξ := mem_genericFiber_of_specializes g hξx hx
  refine ⟨?_, hξ⟩
  by_contra hne
  have hθξ : genericPoint V ≠ E.genericPoint := by
    intro h
    have h1 := AlgebraicGeometry.PrimeDivisor.ringKrullDim_stalk_genericPoint_eq_one E
    have h0 := krullDimLE_zero_stalk_genericPoint V
    rw [Ring.krullDimLE_iff] at h0
    change ringKrullDim (V.presheaf.stalk E.genericPoint) = 1 at h1
    rw [h, h1] at h0
    exact absurd h0 (by decide)
  have h2 := two_le_topologicalKrullDim_of_specializes (S := g.base ⁻¹' {genericPoint W})
    (genericPoint_map_of_surjective g hs) hξ hx
    ((genericPoint_spec V).specializes (Set.mem_univ _)) hξx hθξ (Ne.symm hne)
  have h1 := topologicalKrullDim_genericFiber_eq_one sV sW g hg hs hdim
  rw [(g.fiberHomeo (genericPoint W)).isHomeomorph.topologicalKrullDim_eq] at h1
  rw [h1] at h2
  exact absurd h2 (by decide)

omit [IsIntegral W] [IsIntegral V] [LocallyOfFiniteType sV] [LocallyOfFiniteType sW]
  [CompactSpace W] in
/-- The fibre of a proper morphism over a point `y` is proper over `κ(y)`. -/
theorem isProper_fiberToSpecResidueField [IsProper g] (y : W) :
    IsProper (g.fiberToSpecResidueField y) :=
  inferInstanceAs (IsProper (Limits.pullback.snd g (W.fromSpecResidueField y)))

/-- A prime divisor of `V` meets the generic fibre in a finite set. -/
theorem finite_support_inter_genericFiber (hg : g ≫ sW = sV) (hs : Function.Surjective g)
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1) (E : Mori.PrimeDivisor V) :
    {x | x ∈ (E.support : Set V) ∧ g x = genericPoint W}.Finite :=
  (Set.finite_singleton E.genericPoint).subset fun _ hx =>
    (eq_genericPoint_of_mem_support_of_mem_genericFiber sV sW g hg hs hdim E hx.1 hx.2).1

/-- A point of the generic fibre lying on a prime divisor is a closed point of the generic
fibre. -/
theorem isClosed_singleton_genericFiber (hg : g ≫ sW = sV) (hs : Function.Surjective g)
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1) (E : Mori.PrimeDivisor V)
    {x : V} (hxE : x ∈ (E.support : Set V)) (hx : g x = genericPoint W) :
    IsClosed ({⟨x, hx⟩} : Set (g.base ⁻¹' {genericPoint W})) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hy' : (⟨x, hx⟩ : g.base ⁻¹' {genericPoint W}) ⤳ y := specializes_iff_mem_closure.mpr hy
  rw [subtype_specializes_iff] at hy'
  have hyE : y.1 ∈ (E.support : Set V) := hy'.mem_closed E.idealSheaf.support.isClosed hxE
  refine Subtype.ext ?_
  exact (eq_genericPoint_of_mem_support_of_mem_genericFiber sV sW g hg hs hdim E hyE y.2).1.trans
    (eq_genericPoint_of_mem_support_of_mem_genericFiber sV sW g hg hs hdim E hxE hx).1.symm

end MMP.Flips

namespace MMP.Flips

open MMP.Mori

variable {X : Scheme.{u}}

/-- A rational multiple of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
theorem QDivisor.IsQCartier.qsmul [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X}
    (h : D.IsQCartier) (q : ℚ) : (q • D).IsQCartier := by
  obtain ⟨m, hm, M, hM, hMC⟩ := h
  refine ⟨q.den * m, mul_ne_zero (by exact_mod_cast q.den_ne_zero) hm, q.num • M, ?_,
    hMC.zsmul _⟩
  rw [map_zsmul, hM, smul_smul, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  congr 1
  push_cast
  rw [← Rat.mul_den_eq_num q]
  ring

/-- A finite sum of `ℚ`-Cartier `ℚ`-divisors is `ℚ`-Cartier. -/
theorem QDivisor.isQCartier_sum [IsLocallyNoetherian X] [IsNormal X] {ι : Type*}
    (s : Finset ι)
    (D : ι → QDivisor X) (h : ∀ i ∈ s, (D i).IsQCartier) : (∑ i ∈ s, D i).IsQCartier := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using QDivisor.isQCartier_zero (X := X)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact MMP.Mori.QDivisor.IsQCartier.add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The `ℝ`-linear functional `v ↦ ∑_P c_P v_P` agrees on `ℚ`-divisors with the `ℚ`-linear
functional with the same (rational) coefficients. -/
theorem linearCombination_toRDivisor (c : Mori.PrimeDivisor X → ℚ) (w : QDivisor X) :
    Finsupp.linearCombination ℝ (fun P => (c P : ℝ)) (QDivisor.toRDivisor w) =
      ((Finsupp.linearCombination ℚ c w : ℚ) : ℝ) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, Rat.cast_add]
  | single P a =>
    have : QDivisor.toRDivisor (Finsupp.single P a) = Finsupp.single P (a : ℝ) := by
      classical
      ext E
      change ((Finsupp.single P a E : ℚ) : ℝ) = Finsupp.single P (a : ℝ) E
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp
    rw [this, Finsupp.linearCombination_single, Finsupp.linearCombination_single]
    simp

/-- **An `ℝ`-Cartier `ℚ`-divisor is `ℚ`-Cartier.** If `D = ∑ r_j L_j` with real `r_j` and Cartier
`L_j`, then also `D = ∑ q_j L_j` with rational `q_j` (a linear system over `ℚ` with a real
solution has a rational one), so a positive multiple of `D` is Cartier. -/
theorem QDivisor.isQCartier_of_isCartierCombination [IsLocallyNoetherian X]
    [IsNormal X]
    {D : QDivisor X} (h : IsCartierCombination (QDivisor.toRDivisor D)) : D.IsQCartier := by
  obtain ⟨m, r, L, hL, hD⟩ := h
  let v : Fin m → QDivisor X := fun j => Divisor.toQDivisor (L j)
  have hmem : D ∈ Submodule.span ℚ (Set.range v) := by
    by_contra hnot
    obtain ⟨φ, hφD, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    let c : Mori.PrimeDivisor X → ℚ := fun P => φ (Finsupp.single P 1)
    have hφ : ∀ w, φ w = Finsupp.linearCombination ℚ c w := by
      intro w
      refine LinearMap.congr_fun (Finsupp.lhom_ext fun P a => ?_) w
      simp only [Finsupp.linearCombination_single, c, smul_eq_mul]
      rw [← smul_eq_mul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    have hv : ∀ j, φ (v j) = 0 := by
      intro j
      have : φ (v j) ∈ (Submodule.span ℚ (Set.range v)).map φ :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, rfl⟩)
      rwa [hφp] at this
    apply hφD
    have key := congrArg (Finsupp.linearCombination ℝ (fun P => (c P : ℝ))) hD
    rw [linearCombination_toRDivisor, map_sum] at key
    have hj : ∀ j, Finsupp.linearCombination ℝ (fun P => (c P : ℝ))
        (r j • (L j).mapCoeffs (Int.cast : ℤ → ℝ) Int.cast_zero) = 0 := by
      intro j
      rw [map_smul]
      have : (L j).mapCoeffs (Int.cast : ℤ → ℝ) Int.cast_zero = QDivisor.toRDivisor (v j) := by
        rw [QDivisor.toRDivisor_toQDivisor]; rfl
      rw [this, linearCombination_toRDivisor, ← hφ, hv j]
      simp
    simp only [hj, Finset.sum_const_zero] at key
    rw [hφ]
    exact_mod_cast key
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
  rw [← hq]
  exact QDivisor.isQCartier_sum _ _ fun j _ =>
    QDivisor.IsQCartier.qsmul (QDivisor.isQCartier_toQDivisor (hL j)) (q j)

end MMP.Flips

namespace MMP.Flips

open MMP.Mori

variable {X Y : Scheme.{u}}

/-- A morphism of irreducible schemes restricting to an isomorphism between nonempty opens is
birational. -/
theorem isBirationalMorphism_of_isIso_resLE [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (hU : (U : Set X).Nonempty)
    (hV : (V : Set Y).Nonempty) (h : U ≤ f ⁻¹ᵁ V) (hiso : IsIso (f.resLE V U h)) :
    IsBirationalMorphism f := by
  let e : X.PartialIso Y :=
    { source := U
      dense_source := U.isOpen.dense hU
      target := V
      dense_target := V.isOpen.dense hV
      iso := asIso (f.resLE V U h) }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, U.isOpen.dense hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, asIso_hom, Scheme.Hom.resLE_comp_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- In an irreducible space, the complement of a closed subset of codimension `≥ 2` is
nonempty. -/
theorem nonempty_compl_of_two_le_closedsCodimension {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] (V : Closeds T) (h : 2 ≤ closedsCodimension V) :
    ((V.compl : Opens T) : Set T).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hV : (V : Set T) = Set.univ := by simpa using (hne : ((V : Set T))ᶜ = ∅)
  let W : IrreducibleCloseds T := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩
  have h2 := le_closedsCodimension_iff.mp h W (by rw [hV]; rfl)
  have h0 : codimension W = 0 :=
    Order.coheight_eq_zero.mpr fun b _ => fun x _ => Set.mem_univ x
  rw [h0] at h2
  exact absurd h2 (by decide)

/-- A morphism of irreducible schemes that is an isomorphism outside closed subsets of
codimension `≥ 2` is birational. -/
theorem isBirationalMorphism_of_exists_isIso [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (H : ∃ (V : Closeds X) (W : Closeds Y), 2 ≤ closedsCodimension V ∧
      2 ≤ closedsCodimension W ∧ ∃ h : V.compl ≤ f ⁻¹ᵁ W.compl, IsIso (f.resLE W.compl V.compl h)) :
    IsBirationalMorphism f := by
  obtain ⟨V, W, hV, hW, h, hiso⟩ := H
  exact isBirationalMorphism_of_isIso_resLE f _ _ (nonempty_compl_of_two_le_closedsCodimension V hV)
    (nonempty_compl_of_two_le_closedsCodimension W hW) h hiso

variable {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))

/-- A small birational contraction is a birational morphism. -/
theorem IsSmall.isBirationalMorphism {f : Y ⟶ X} (h : IsSmall k sX sY f) :
    IsBirationalMorphism f := by
  have := h.isVariety_source.toIsIntegral
  have := h.isVariety_target.toIsIntegral
  exact isBirationalMorphism_of_exists_isIso f h.exists_isIso

end MMP.Flips

namespace MMP.Flips

/-- The normalization of a scheme `C` locally of finite type over a perfect field `k`, all of
whose irreducible components have dimension at most one, is smooth over `k`: it is normal of
dimension at most one, hence regular, and regular schemes locally of finite type over a perfect
field are smooth (FA 12.2.9). -/
theorem smooth_normalization_comp_of_dim_le_one {k : Type u} [Field k] [PerfectField k]
    {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) [LocallyOfFiniteType sC]
    (hdim : ∀ Z ∈ irreducibleComponents C, topologicalKrullDim Z ≤ 1)
    (hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite) :
    Smooth (C.normalization hC ≫ sC) := by
  have : IsFinite (normalizationOverField k sC) := isFinite_normalizationOverField k sC
  have : IsLocallyNoetherian (normalizationSchemeOverField k sC) :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizationOverField k sC ≫ sC)
  have : IsNormal (normalizationSchemeOverField k sC) := Scheme.isNormal_normalizationScheme C _
  exact smooth_of_isRegular_over_perfectField (normalizationOverField k sC ≫ sC)
    (isRegular_of_isNormal_of_topologicalKrullDim_le_one _
      (topologicalKrullDim_normalizationScheme_le_one
        (topologicalKrullDim_le_of_forall_mem_irreducibleComponents hdim) _))

end MMP.Flips
