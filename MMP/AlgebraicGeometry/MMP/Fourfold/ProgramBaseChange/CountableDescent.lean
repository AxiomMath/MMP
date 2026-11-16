module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.MMP.Fourfold.ProgramBaseChange.AlgClosedExtension
import MMP.AlgebraicGeometry.SpreadingOut.CountableFieldOfDefinition
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous

/-!
# Descent of a countable program to a countable algebraically closed field

Let `k` be an algebraically closed field of characteristic zero and `𝒫` a program from a
projective lc pair `(X, B)` over `k` (`MMP.Fourfold.Program`), with its rays, contractions and
permitted steps. A program has countably many indices, and each index is described by finitely
many equations, so all of `𝒫` is defined over a countable algebraically closed subfield
`k₀ ⊆ k`: there is a program `𝒫₀` over `k₀`, with the same number of birational steps, whose
base change to `k` is `𝒫`. The boundaries of `𝒫` are the base changes of those of `𝒫₀`, so
they carry the same coefficients.

## Main results

* `MMP.Fourfold.Program.exists_countable_isAlgClosed_subfield_program`: the descent.

## Implementation notes

Base change along `k₀ → k` is recorded by pullback squares over
`Spec k ⟶ Spec k₀`: one for each model `X_i` (`i ≤ n`), each target `Z_i` (`i < n`) and the
target `T` of the final contraction, with the contractions and the small morphisms commuting
with the projections. A Weil divisor `D` on `X_i` is the base change of `D₀` on the
corresponding model over `k₀` when every prime divisor `E` whose generic point lies over the
generic point of a prime divisor `E₀` has coefficient `D₀(E₀)`, and every other prime divisor
has coefficient `0`; since `k₀` is algebraically closed, `E` is then `π⁻¹(E₀)`. A ray is
transported by the linear map `φ : N₁(X₀)_ℝ → N₁(X)_ℝ` characterised by
`φ [C₀] = [(C₀)_k]`, as in `MMP.Fourfold.map_closedConeOfCurves_eq_of_isPullback`. The
models are indexed by the numbers of birational steps, which agree, so the final contraction
is compared through `eqToHom` of that equality.

The proof spreads out one countable diagram of schemes of finite type over `k`, by
`MMP.FieldOfDefinition.exists_countable_isAlgClosed_model`. The diagram is indexed by a thin
category in which no two non-identity arrows compose. Each model `X_i` has a copy `X'_i`, which
receives the identity `X_i ⟶ X'_i` and the closed immersions of the finitely many prime
divisors in the supports of `K_i` and `B_i`. The contractions run from the `X_i` to the `Z_i`
and to `T`, and indices that the program does not constrain go to `Spec k`. Every support prime
is the base change of a closed subscheme over `k₀`, so its generic point does not lie over the
generic point of the model over `k₀`; it is therefore the base change of a prime divisor, and the
divisors descend coefficientwise. The rays descend through
`MMP.Fourfold.numericalCurveClassesBaseChange`, and
`MMP.Fourfold.program_conditions_iff_of_isPullback` shows that the descended data form a program.

## References

* [KM98] Kollár, Mori, *Birational Geometry of Algebraic Varieties*.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori

namespace MMP.Fourfold

universe u

section Square

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] {X W : Scheme.{u}}
  (f : X ⟶ Spec (.of k₀)) [LocallyOfFiniteType f] {p : W ⟶ X} {s : W ⟶ Spec (.of K)}

/-- The preimage of a locally closed subset under the projection of a base change of the ground
field has the same dimension. -/
private lemma topologicalKrullDim_preimage_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) {Z : Set X}
    (hZ : IsLocallyClosed Z) : topologicalKrullDim (p ⁻¹' Z) = topologicalKrullDim Z := by
  obtain ⟨-, -, -, -, hdim⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) f
  rw [← hdim Z hZ]
  have hp (w : W) : p w = pullback.fst f _ (h.isoPullback.hom w) := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
  refine (Homeomorph.subtype (Scheme.homeoOfIso h.isoPullback) fun w => ?_).isHomeomorph
    |>.topologicalKrullDim_eq
  simp only [Set.mem_preimage, Scheme.homeoOfIso_apply]
  rw [hp w]

/-- The preimage of an irreducible closed subset under the projection of a base change of an
algebraically closed ground field is irreducible. -/
private lemma isIrreducible_preimage_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) {Z : Set X}
    (hZc : IsClosed Z) (hZ : IsIrreducible Z) : IsIrreducible (p ⁻¹' Z) := by
  let C : TopologicalSpace.Closeds X := ⟨Z, hZc⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  have : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible C hZ
  have : LocallyOfFiniteType (I.subschemeι ≫ f) := inferInstance
  have hsq : IsPullback (pullback.snd p I.subschemeι) (pullback.fst p I.subschemeι ≫ s)
      (I.subschemeι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) :=
    (IsPullback.of_hasPullback p I.subschemeι).flip.paste_vert h
  obtain ⟨-, hint, -⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) (I.subschemeι ≫ f)
  have : IsIntegral (pullback (I.subschemeι ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) := hint.1 ‹_›
  have : IsIntegral (pullback p I.subschemeι) := MMP.isIntegral_of_iso hsq.isoPullback.symm
  have hr : Set.range (pullback.fst p I.subschemeι) = p ⁻¹' Z := by
    rw [Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn

/-- Under a base change of an algebraically closed ground field of an integral scheme, coheights
can only grow, and every point has a preimage of the same coheight (the generic point of its
preimage closure). -/
private lemma coheight_le_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) [IsIntegral X]
    [IsIntegral W] [LocallyOfFiniteType s] [Surjective p] :
    (∀ w : W, Order.coheight (p w) ≤ Order.coheight w) ∧
      ∀ x : X, ∃ w, p w = x ∧ Order.coheight w ≤ Order.coheight x := by
  have hD : topologicalKrullDim W = topologicalKrullDim X :=
    (MMP.ProgramBaseChange.invariants_of_isPullback f h).2.2
  have hn := MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg f
  have hX (x : X) := (MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight f x).trans hn
  have hW (w : W) := ((MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s w).trans
    hD).trans hn
  have hcl (x : X) : topologicalKrullDim (p ⁻¹' closure {x}) =
      topologicalKrullDim (closure {x} : Set X) :=
    topologicalKrullDim_preimage_of_isPullback f h isClosed_closure.isLocallyClosed
  constructor
  · intro w
    have hsub : closure {w} ⊆ p ⁻¹' closure {p w} :=
      closure_minimal (Set.singleton_subset_iff.mpr (subset_closure rfl))
        (isClosed_closure.preimage p.continuous)
    have hle : topologicalKrullDim (closure {w} : Set W) ≤
        topologicalKrullDim (closure {p w} : Set X) := by
      rw [← hcl]
      exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
    exact MMP.ProgramBaseChange.le_of_add_eq_add_of_le (hW w) (hX (p w)) hle
  · intro x
    have hirr := isIrreducible_preimage_of_isPullback f h (isClosed_closure (s := {x}))
      isIrreducible_singleton.closure
    obtain ⟨w, hw⟩ := QuasiSober.sober hirr (isClosed_closure.preimage p.continuous)
    refine ⟨w, MMP.ProgramBaseChange.map_eq_of_closure_eq hw.def, ?_⟩
    have heq : topologicalKrullDim (closure {w} : Set W) =
        topologicalKrullDim (closure {x} : Set X) := by
      rw [← hcl, ← hw.def]
    exact MMP.ProgramBaseChange.le_of_add_eq_add_of_le (hX x) (hW w) heq.ge

end Square

section Helpers

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀]

/-! ### Prime divisors under base change -/

/-- The base change of a prime divisor: `π⁻¹(closure P₀)` is the closure of the generic point of a
prime divisor of `X`, lying over the generic point of `P₀`. -/
private theorem exists_primeDivisor_baseChange {X₀ X : Scheme.{u}} [IsIntegral X₀] [IsIntegral X]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (P₀ : MMP.Mori.PrimeDivisor X₀) :
    ∃ P : MMP.Mori.PrimeDivisor X, closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} ∧
      π P.genericPoint = P₀.genericPoint := by
  have : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  have : Surjective π := MMP.ProgramBaseChange.surjective_of_isPullback h
  set x := P₀.genericPoint
  have hirr := isIrreducible_preimage_of_isPullback s₀ h (isClosed_closure (s := {x}))
    isIrreducible_singleton.closure
  obtain ⟨w, hw⟩ := QuasiSober.sober hirr (isClosed_closure.preimage π.continuous)
  have hpw : π w = x := MMP.ProgramBaseChange.map_eq_of_closure_eq hw.def
  obtain ⟨h1, h2⟩ := coheight_le_of_isPullback s₀ h
  obtain ⟨w', hw'x, hw'⟩ := h2 x
  have hww' : w ⤳ w' := by
    rw [specializes_iff_mem_closure, hw.def]
    show π w' ∈ closure {x}
    rw [hw'x]; exact subset_closure rfl
  have hcoh : Order.coheight w = 1 := by
    have hx1 : Order.coheight x = 1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P₀
    have hle : Order.coheight w ≤ Order.coheight w' := Order.coheight_anti hww'
    refine le_antisymm (hle.trans (hw'.trans hx1.le)) ?_
    rw [← hx1, ← hpw]
    exact h1 w
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hcoh, ?_, ?_⟩
  · change closure {(AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hcoh).genericPoint} = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hw.def
  · change π (AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hcoh).genericPoint = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hpw

/-- **Prime divisors over a point of codimension one are base changes.** A prime divisor of the
base change `X` whose generic point does not lie over the generic point of `X₀` is the base
change of a prime divisor of `X₀`. -/
private theorem exists_closure_eq_of_map_ne_genericPoint {X₀ X : Scheme.{u}} [IsIntegral X₀]
    [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (P : MMP.Mori.PrimeDivisor X) (hP : π P.genericPoint ≠ genericPoint X₀) :
    ∃ P₀ : MMP.Mori.PrimeDivisor X₀,
      closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} := by
  have : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  have : Surjective π := MMP.ProgramBaseChange.surjective_of_isPullback h
  obtain ⟨h1, -⟩ := coheight_le_of_isPullback s₀ h
  have hP1 : Order.coheight P.genericPoint = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  have hx : Order.coheight (π P.genericPoint) = 1 := by
    refine le_antisymm (hP1 ▸ h1 _) ?_
    have hgen : genericPoint X₀ ⤳ π P.genericPoint := (genericPoint_spec X₀).specializes trivial
    have hle : π P.genericPoint ≤ genericPoint X₀ := hgen
    have hlt : π P.genericPoint < genericPoint X₀ :=
      lt_of_le_not_ge hle fun h' => hP (hgen.antisymm h').eq.symm
    exact le_add_self.trans (Order.coheight_add_one_le hlt)
  obtain ⟨P', hP'c, hP'π⟩ := exists_primeDivisor_baseChange h
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx)
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx, ?_⟩
  have hgp : (AlgebraicGeometry.PrimeDivisor.ofCoheightOne (π P.genericPoint) hx).genericPoint =
      π P.genericPoint := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hsp : P'.genericPoint ⤳ P.genericPoint := by
    rw [specializes_iff_mem_closure, hP'c, Set.mem_preimage]
    change π P.genericPoint ∈ closure {(AlgebraicGeometry.PrimeDivisor.ofCoheightOne
      (π P.genericPoint) hx).genericPoint}
    rw [hgp]; exact subset_closure rfl
  have heq := MMP.ProgramBaseChange.eq_of_specializes_of_coheight_eq_one hsp
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P') hP1
  rw [← hP'c, heq]

end Helpers

/-! ### Pullback squares of schemes -/

/-- In a pullback square of schemes, the range of the first projection is the preimage of the
range of the opposite side. -/
private theorem range_fst_of_isPullback {P' X₁ Y₁ Z₁ : Scheme.{u}} {fst : P' ⟶ X₁}
    {snd : P' ⟶ Y₁} {f : X₁ ⟶ Z₁} {g : Y₁ ⟶ Z₁} (h : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  have hs : Function.Surjective h.isoPullback.hom :=
    (Scheme.homeoOfIso h.isoPullback).surjective
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    hs.range_eq, Set.image_univ, Scheme.Pullback.range_fst]

/-- Precomposing the first projection of a pullback square with an identification of objects of
an over category. -/
private theorem isPullback_eqToHom_left_comp {S T W : Scheme.{u}} {A O : Over S} (hAO : A = O)
    {q : O.left ⟶ W} {t : W ⟶ T} {g : S ⟶ T} (h : IsPullback q O.hom t g) :
    IsPullback ((eqToHom hAO).left ≫ q) A.hom t g := by
  subst hAO
  simpa using h

/-- **A support prime is not over the generic point.** Let `π : X ⟶ X₀` be a surjective morphism
of irreducible schemes, and `ι : D ⟶ X` a morphism with range `closure {x}` for a point `x` other
than the generic point of `X`. If `ι` is the base change along `π ≫ c` of some `d₀ : D₀ ⟶ X₁`,
then `π x` is not the generic point of `X₀`. -/
private theorem map_ne_genericPoint_of_isPullback {X X₀ X₁ D D₀ : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace X₀] (π : X ⟶ X₀) [Surjective π] (c : X₀ ⟶ X₁)
    {ι : D ⟶ X} {pD : D ⟶ D₀} {d₀ : D₀ ⟶ X₁} (h : IsPullback ι pD (π ≫ c) d₀) {x : X}
    (hx : Set.range ι = closure {x}) (hne : x ≠ genericPoint X) :
    π x ≠ genericPoint X₀ := by
  intro hπx
  have : IsDominant π := ⟨π.surjective.denseRange⟩
  have hgen : π (genericPoint X) = genericPoint X₀ := map_genericPoint_of_isDominant π
  have hxr : x ∈ Set.range ι := hx ▸ subset_closure rfl
  obtain ⟨y, rfl⟩ := hxr
  have hmem : (π ≫ c) (genericPoint X) ∈ Set.range d₀ := by
    refine ⟨pD y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, hπx, hgen]
  rw [← Set.mem_preimage, ← range_fst_of_isPullback h, hx] at hmem
  exact hne ((specializes_iff_mem_closure.mpr hmem).antisymm
    ((genericPoint_spec X).specializes trivial)).eq

/-- Replacing the right side of a pullback square by an isomorphic object. -/
private theorem isPullback_comp_inv {P' W W' Y₁ Z₁ : Scheme.{u}} {fst : P' ⟶ W}
    {snd : P' ⟶ Y₁} {f : W ⟶ Z₁} {g : Y₁ ⟶ Z₁} (h : IsPullback fst snd f g) (e : W' ≅ W) :
    IsPullback (fst ≫ e.inv) snd (e.hom ≫ f) g := by
  have h2 : IsPullback e.inv f (e.hom ≫ f) (𝟙 Z₁) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using h.paste_horiz h2

/-- The generic point of an integral scheme has coheight zero. -/
private lemma coheight_genericPoint_eq_zero (Y : Scheme.{u}) [IsIntegral Y] :
    Order.coheight (genericPoint Y) = 0 :=
  Order.coheight_eq_zero.mpr fun _ _ => (genericPoint_spec Y).specializes trivial

/-- The generic point of a prime divisor is not the generic point of the scheme. -/
private lemma genericPoint_ne_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (E : MMP.Mori.PrimeDivisor Y) : E.genericPoint ≠ genericPoint Y := by
  intro h
  have h1 : Order.coheight (AlgebraicGeometry.PrimeDivisor.genericPoint E) = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  change Order.coheight E.genericPoint = 1 at h1
  rw [h, coheight_genericPoint_eq_zero] at h1
  exact zero_ne_one h1

/-- **Support primes descend.** Let `π : X ⟶ X₀` be a base change along `Spec K ⟶ Spec k₀` of
integral schemes. A prime divisor `E` of `X` whose closed immersion is the base change, along
`π ≫ c`, of some `d₀ : D₀ ⟶ X₁`, is the base change of a prime divisor of `X₀`. -/
private theorem exists_closure_eq_of_isPullback_subschemeι {k₀ K : Type u} [Field k₀] [Field K]
    [Algebra k₀ K] [IsAlgClosed k₀] {X₀ X X₁ D₀ : Scheme.{u}} [IsIntegral X₀] [IsIntegral X]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) (c : X₀ ⟶ X₁)
    (E : MMP.Mori.PrimeDivisor X) {pD : E.idealSheaf.subscheme ⟶ D₀} {d₀ : D₀ ⟶ X₁}
    (hE : IsPullback E.idealSheaf.subschemeι pD (π ≫ c) d₀) :
    ∃ E₀ : MMP.Mori.PrimeDivisor X₀,
      closure {E.genericPoint} = π.base ⁻¹' closure {E₀.genericPoint} := by
  have : Surjective π := MMP.ProgramBaseChange.surjective_of_isPullback h
  have hx : Set.range E.idealSheaf.subschemeι = closure {E.genericPoint} := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact AlgebraicGeometry.PrimeDivisor.support_eq_closure E
  exact exists_closure_eq_of_map_ne_genericPoint h E
    (map_ne_genericPoint_of_isPullback π c hE hx (genericPoint_ne_genericPoint E))

/-! ### Descent of divisors -/

section DescendDivisor

variable {R : Type*} [Zero R] {X₀ X : Scheme.{u}} (π : X ⟶ X₀)

open Classical in
/-- The descent of a divisor `D` on `X` along a surjective `π : X ⟶ X₀`: the coefficient at a
prime divisor `E₀` of `X₀` is the coefficient of `D` at the prime divisor of `X` with closure
`π⁻¹(E₀)`, if there is one, and `0` otherwise. -/
private noncomputable def descendDivisor (D : DivisorWithCoeffs R X) : DivisorWithCoeffs R X₀ :=
  if hπ : Function.Surjective π then
    Finsupp.ofSupportFinite (fun E₀ => if h : ∃ E : MMP.Mori.PrimeDivisor X,
        closure {E.genericPoint} = π.base ⁻¹' closure {E₀.genericPoint} then D h.choose else 0)
      (by
        haveI : Surjective π := ⟨hπ⟩
        refine (D.support.finite_toSet.biUnion fun E _ =>
          (?_ : Set.Subsingleton {E₀ : MMP.Mori.PrimeDivisor X₀ |
            closure {E.genericPoint} = π.base ⁻¹' closure {E₀.genericPoint}}).finite).subset ?_
        · intro E₀ h₀ E₁ h₁
          exact MMP.ProgramBaseChange.primeDivisor_eq_of_closure_eq h₀ h₁
        · intro E₀ hE₀
          simp only [Function.mem_support] at hE₀
          split_ifs at hE₀ with h
          · exact Set.mem_biUnion (Finsupp.mem_support_iff.mpr hE₀) h.choose_spec
          · exact absurd rfl hE₀)
  else 0

/-- The coefficient of the descent of `D` at `E₀` is the coefficient of `D` at the base change
of `E₀`. -/
private theorem descendDivisor_apply [Surjective π] (D : DivisorWithCoeffs R X)
    {E₀ : MMP.Mori.PrimeDivisor X₀} {E : MMP.Mori.PrimeDivisor X}
    (h : closure {E.genericPoint} = π.base ⁻¹' closure {E₀.genericPoint}) :
    descendDivisor π D E₀ = D E := by
  classical
  have hex : ∃ E : MMP.Mori.PrimeDivisor X,
      closure {E.genericPoint} = π.base ⁻¹' closure {E₀.genericPoint} := ⟨E, h⟩
  rw [descendDivisor, dif_pos π.surjective, Finsupp.ofSupportFinite_coe, dif_pos hex,
    MMP.ProgramBaseChange.primeDivisor_eq_of_closure_eq' hex.choose_spec h]

end DescendDivisor

/-! ### Curve classes under base change -/

/-- The base-extension map of curve classes is determined by its characterising property. -/
private theorem eq_of_forall_closure_eq {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]
    [IsAlgClosed k₀] {X₀ X : Scheme.{u}} {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)}
    {π : X ⟶ X₀} (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {φ ψ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s}
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) = OneCycle.numericalClass s (C.cycle ℝ))
    (hψ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        ψ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) = OneCycle.numericalClass s (C.cycle ℝ)) :
    φ = ψ := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle s₀ fun C₀ => ?_
  obtain ⟨C, hC, -⟩ := MMP.ProgramBaseChange.exists_properCurve_baseChange s₀ s π h C₀
  rw [hφ C₀ C hC, hψ C₀ C hC]

/-- If a linear equivalence carries the cone `C` onto `C'`, its inverse carries subsets of `C'`
into `C`. -/
private theorem symm_image_subset_of_map_eq {M N : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N] (e : M ≃ₗ[ℝ] N) {C : PointedCone ℝ M} {C' : PointedCone ℝ N}
    (hc : C.map e.toLinearMap = C') {S : Set N} (hS : S ⊆ C') : e.symm '' S ⊆ C := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := (hc ▸ hS hx : x ∈ C.map e.toLinearMap)
  simpa using hy

/-! ### Sequences of models -/

/-- The sequence of models `modelSeq (G 0) (G ∘ succ)` is `G`. -/
private def modelSeqIso (G : ℕ → Scheme.{u}) :
    ∀ i, modelSeq (G 0) (fun i => G (i + 1)) i ≅ G i
  | 0 => Iso.refl _
  | _ + 1 => Iso.refl _

private theorem modelSeqIso_hom_comp_hom {k : Type u} [Field k] (H : ℕ → Over (Spec (.of k)))
    (i : ℕ) : (modelSeqIso (fun i => (H i).left) i).hom ≫ (H i).hom =
      modelStr (H 0).hom (fun i => (H (i + 1)).hom) i := by
  cases i <;> exact Category.id_comp _

/-! ### The shape of the diagram of a program -/

/-- The nodes of the diagram of a program: the models `X i`, their copies `X' i`, the targets
`Z i`, the final target `T`, and the prime divisors `D i E`, `E : S i`, of the `i`-th model;
`n` is the number of birational steps, which decides the arrow into `T`. -/
private inductive Node (S : ℕ → Type u) (n : ℕ∞) : Type u
  | X (i : ℕ)
  | X' (i : ℕ)
  | Z (i : ℕ)
  | T
  | D (i : ℕ) (E : S i)

namespace Node

variable {S : ℕ → Type u} {n : ℕ∞}

/-- An injection of the nodes into a countable type when every `S i` is countable. -/
private def code : Node S n → ℕ ⊕ ℕ ⊕ ℕ ⊕ PUnit.{1} ⊕ (Σ i, S i)
  | X i => .inl i
  | X' i => .inr (.inl i)
  | Z i => .inr (.inr (.inl i))
  | T => .inr (.inr (.inr (.inl PUnit.unit)))
  | D i E => .inr (.inr (.inr (.inr ⟨i, E⟩)))

private theorem code_injective : Function.Injective (code (S := S) (n := n)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [code]

/-- The arrows of the diagram that are not identities, for `n` birational steps: `X i ⟶ X' i`,
`X i ⟶ Z i`, `X (i + 1) ⟶ Z i`, `X n ⟶ T` and `D i E ⟶ X' i`. -/
private def Step : Node S n → Node S n → Prop
  | X i, X' j => i = j
  | X i, Z j => i = j ∨ i = j + 1
  | X i, T => i = n.toNat
  | D i _, X' j => i = j
  | _, _ => False

private theorem not_step_step {a b c : Node S n} (h : Step a b) (h' : Step b c) :
    False := by
  cases a <;> cases b <;> cases c <;> simp [Step] at h h'

private theorem ne_of_step {a b : Node S n} (h : Step a b) : a ≠ b := by
  rintro rfl
  cases a <;> simp [Step] at h

end Node

/-- The nodes of the diagram, ordered by the arrows of `Node.Step`; no two non-identity arrows
compose, so this is a preorder. -/
private abbrev Node.preorder (S : ℕ → Type u) (n : ℕ∞) : Preorder (Node S n) where
  le a b := a = b ∨ Node.Step a b
  le_refl _ := Or.inl rfl
  le_trans a b c := by
    rintro (rfl | h) (rfl | h')
    · exact Or.inl rfl
    · exact Or.inr h'
    · exact Or.inr h
    · exact (Node.not_step_step h h').elim

attribute [local instance] Node.preorder

private theorem Node.countableCategory (S : ℕ → Type u) [∀ i, Countable (S i)] (n : ℕ∞) :
    CountableCategory (Node S n) where
  countableObj := Node.code_injective.countable
  countableHom _ _ := inferInstance

private theorem Node.le_iff {S : ℕ → Type u} {n : ℕ∞} {a b : Node S n} :
    a ≤ b ↔ a = b ∨ Node.Step a b := Iff.rfl

/-! ### The diagram of a program -/

section Diagram

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {K : Divisor X} {B : QDivisor X}
  (P : Program sX K B)

open Classical

/-- The prime divisors in the supports of `K_i` and `B_i`. -/
private noncomputable def suppPrimes (i : ℕ) : Finset (MMP.Mori.PrimeDivisor (modelSeq X P.Y i)) :=
  (divisorSeq K P.KY i).support ∪ (divisorSeq B P.BY i).support

/-- The prime divisors in the supports of `K_i` and `B_i`, as a type. -/
private abbrev Supp (i : ℕ) : Type u := {E // E ∈ suppPrimes P i}

/-- The nodes the program constrains. -/
private def Valid : Node (Supp P) P.n → Prop
  | .X i | .X' i | .D i _ => (i : ℕ∞) ≤ P.n
  | .Z i => (i : ℕ∞) < P.n
  | .T => P.hasFinal

/-- The scheme of a node, over `k`. -/
private noncomputable def real : Node (Supp P) P.n → Over (Spec (.of k))
  | .X i | .X' i => Over.mk (modelStr sX P.sY i)
  | .Z i => Over.mk (P.sZ i)
  | .T => Over.mk P.sT
  | .D i E => Over.mk (E.1.idealSheaf.subschemeι ≫ modelStr sX P.sY i)

/-- The object of the diagram at a node: its scheme if the node is constrained, `Spec k`
otherwise. -/
private noncomputable def obj (a : Node (Supp P) P.n) : Over (Spec (.of k)) :=
  if Valid P a then real P a else Over.mk (𝟙 _)

private theorem obj_of_valid {a : Node (Supp P) P.n} (h : Valid P a) : obj P a = real P a :=
  if_pos h

private theorem obj_of_not_valid {a : Node (Supp P) P.n} (h : ¬ Valid P a) :
    obj P a = Over.mk (𝟙 _) :=
  if_neg h

/-- The comparison `real a ⟶ obj a`: the identification for a constrained node, the structure
morphism otherwise. -/
private noncomputable def toObj (a : Node (Supp P) P.n) : real P a ⟶ obj P a :=
  if h : Valid P a then eqToHom (obj_of_valid P h).symm
  else Over.mkIdTerminal.from _ ≫ eqToHom (obj_of_not_valid P h).symm

private theorem toObj_of_valid {a : Node (Supp P) P.n} (h : Valid P a) :
    toObj P a = eqToHom (obj_of_valid P h).symm :=
  dif_pos h

/-- A model `X_i` with `i ≤ n` is a projective variety. -/
private theorem isProjectiveVariety_model {i : ℕ} (hi : (i : ℕ∞) ≤ P.n) :
    MMP.Mori.IsProjectiveVariety k (modelStr sX P.sY i) := by
  cases i with
  | zero => exact P.isProjectiveVariety
  | succ j =>
    have hj : (j : ℕ∞) < P.n := by
      refine lt_of_lt_of_le ?_ hi
      exact_mod_cast Nat.lt_succ_self j
    exact (P.isPermittedStep j hj).isProjectiveVariety_step

private theorem valid_of_step {a b : Node (Supp P) P.n} (h : Node.Step a b) (hb : Valid P b) :
    Valid P a := by
  cases a <;> cases b <;> simp only [Node.Step] at h <;> simp only [Valid] at hb ⊢
  · exact h ▸ hb
  · rcases h with rfl | rfl
    · exact hb.le
    · exact Order.add_one_le_of_lt hb
  · subst h
    exact ENat.coe_toNat_le_self P.n
  · exact h ▸ hb

/-- The non-identity arrows between the schemes of the nodes: the identity `X i ⟶ X' i`, the
contraction `f_i`, the small morphism `f_i⁺`, the final contraction `g` and the closed immersion
of a prime divisor. -/
private noncomputable def realMap :
    ∀ a b : Node (Supp P) P.n, Node.Step a b → Valid P b → (real P a ⟶ real P b)
  | .X i, .X' j, h, _ => eqToHom (by subst h; rfl)
  | .X i, .Z j, h, hb =>
    if h' : i = j then by
      subst h'
      exact Over.homMk (P.f i) (P.isPermittedStep i hb).isContractionOfRay.comp_eq
    else by
      obtain rfl : i = j + 1 := h.resolve_left h'
      exact Over.homMk (P.fp j) (P.isPermittedStep j hb).isSmallMorphism_step.comp_eq
  | .X i, .T, h, hb => by
      subst h
      exact Over.homMk P.g (P.final_spec hb).2.2.1.comp_eq
  | .D i E, .X' j, h, _ => by
      subst h
      exact Over.homMk E.1.idealSheaf.subschemeι rfl
  | .X _, .X _, h, _ | .X _, .D _ _, h, _ => h.elim
  | .X' _, .X _, h, _ | .X' _, .X' _, h, _ | .X' _, .Z _, h, _ | .X' _, .T, h, _
  | .X' _, .D _ _, h, _ => h.elim
  | .Z _, .X _, h, _ | .Z _, .X' _, h, _ | .Z _, .Z _, h, _ | .Z _, .T, h, _
  | .Z _, .D _ _, h, _ => h.elim
  | .T, .X _, h, _ | .T, .X' _, h, _ | .T, .Z _, h, _ | .T, .T, h, _ | .T, .D _ _, h, _ => h.elim
  | .D _ _, .X _, h, _ | .D _ _, .Z _, h, _ | .D _ _, .T, h, _ | .D _ _, .D _ _, h, _ => h.elim

/-- The arrow of the diagram along a non-identity arrow of the shape. -/
private noncomputable def stepMap (a b : Node (Supp P) P.n) (h : Node.Step a b) :
    obj P a ⟶ obj P b :=
  if hb : Valid P b then
    eqToHom (obj_of_valid P (valid_of_step P h hb)) ≫ realMap P a b h hb ≫
      eqToHom (obj_of_valid P hb).symm
  else Over.mkIdTerminal.from _ ≫ eqToHom (obj_of_not_valid P hb).symm

/-- The diagram of a program, over `Spec k`. -/
private noncomputable def diagram : Node (Supp P) P.n ⥤ Over (Spec (.of k)) where
  obj := obj P
  map {a b} h := if hab : a = b then eqToHom (congrArg (obj P) hab) else
    stepMap P a b ((Node.le_iff.mp (leOfHom h)).resolve_left hab)
  map_id a := by simp
  map_comp {a b c} f g := by
    by_cases hab : a = b
    · subst hab
      rw [show f ≫ g = g from Subsingleton.elim _ _, dif_pos rfl, eqToHom_refl, Category.id_comp]
    by_cases hbc : b = c
    · subst hbc
      rw [show f ≫ g = f from Subsingleton.elim _ _, dif_pos (rfl : b = b), eqToHom_refl,
        Category.comp_id]
    exact (Node.not_step_step ((Node.le_iff.mp (leOfHom f)).resolve_left hab)
      ((Node.le_iff.mp (leOfHom g)).resolve_left hbc)).elim

private theorem stepMap_of_valid {a b : Node (Supp P) P.n} (hs : Node.Step a b)
    (hb : Valid P b) :
    stepMap P a b hs = eqToHom (obj_of_valid P (valid_of_step P hs hb)) ≫ realMap P a b hs hb ≫
      eqToHom (obj_of_valid P hb).symm :=
  dif_pos hb

/-- Along a non-identity arrow into a constrained node, the diagram is `realMap`. -/
private theorem toObj_comp_diagram_map {a b : Node (Supp P) P.n}
    (h : a ⟶ b)
    (hs : Node.Step a b) (hb : Valid P b) :
    toObj P a ≫ (diagram P).map h = realMap P a b hs hb ≫ toObj P b := by
  have hmap : (diagram P).map h = stepMap P a b hs := dif_neg (Node.ne_of_step hs)
  rw [hmap]
  change (toObj P a ≫ stepMap P a b hs : real P a ⟶ obj P b) = _
  rw [stepMap_of_valid P hs hb, toObj_of_valid P hb,
    toObj_of_valid P (valid_of_step P hs hb), ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]

private theorem realMap_X_X' (i : ℕ) (h : Node.Step (Node.X i : Node (Supp P) P.n) (.X' i))
    (hb : Valid P (.X' i)) : (realMap P (.X i) (.X' i) h hb).left = 𝟙 _ := by
  simp only [realMap, Comma.eqToHom_left]
  rfl

private theorem realMap_X_X'_comp (i : ℕ)
    (h : Node.Step (Node.X i : Node (Supp P) P.n) (.X' i)) (hb : Valid P (.X' i))
    {W : Scheme.{u}} (q : (real P (.X' i)).left ⟶ W) :
    (realMap P (.X i) (.X' i) h hb).left ≫ q = q := by
  rw [realMap_X_X']
  exact Category.id_comp q

private theorem realMap_X_Z (i : ℕ) (h : Node.Step (Node.X i : Node (Supp P) P.n) (.Z i))
    (hb : Valid P (.Z i)) : (realMap P (.X i) (.Z i) h hb).left = P.f i := by
  simp only [realMap, dif_pos rfl]
  rfl

private theorem realMap_X_succ_Z (i : ℕ)
    (h : Node.Step (Node.X (i + 1) : Node (Supp P) P.n) (.Z i)) (hb : Valid P (.Z i)) :
    (realMap P (.X (i + 1)) (.Z i) h hb).left = P.fp i := by
  simp only [realMap, dif_neg (Nat.succ_ne_self i)]
  rfl

private theorem realMap_X_T (h : Node.Step (Node.X P.n.toNat : Node (Supp P) P.n) .T)
    (hb : Valid P .T) : (realMap P (.X P.n.toNat) .T h hb).left = P.g := rfl

private theorem realMap_D_X' (i : ℕ) (E : Supp P i)
    (h : Node.Step (Node.D i E : Node (Supp P) P.n) (.X' i)) (hb : Valid P (.X' i)) :
    (realMap P (.D i E) (.X' i) h hb).left = E.1.idealSheaf.subschemeι := rfl

/-- The schemes of the diagram are of finite type over `k`. -/
private theorem locallyOfFiniteType_obj (a : Node (Supp P) P.n) :
    LocallyOfFiniteType (obj P a).hom ∧ QuasiCompact (obj P a).hom := by
  by_cases ha : Valid P a
  · rw [obj_of_valid P ha]
    have key : ∀ {Y : Scheme.{u}} (t : Y ⟶ Spec (.of k)), MMP.Mori.IsProjectiveVariety k t →
        LocallyOfFiniteType t ∧ QuasiCompact t := fun t ht => by
      obtain ⟨⟨-, -, h1, h2⟩, -⟩ :=
        (MMP.Mori.isProjectiveVariety_iff k t).1 ht |>.imp_left (MMP.Mori.isVariety_iff k t).1
      exact ⟨h1, h2⟩
    cases a with
    | X i => exact key _ (isProjectiveVariety_model P ha)
    | X' i => exact key _ (isProjectiveVariety_model P ha)
    | Z i => exact key _ (P.isPermittedStep i ha).isProjectiveVariety_target
    | T => exact key _ (P.final_spec ha).2.2.2.1
    | D i E =>
      obtain ⟨h1, h2⟩ := key _ (isProjectiveVariety_model P ha)
      change LocallyOfFiniteType (E.1.idealSheaf.subschemeι ≫ modelStr sX P.sY i) ∧
        QuasiCompact (E.1.idealSheaf.subschemeι ≫ modelStr sX P.sY i)
      exact ⟨inferInstance, inferInstance⟩
  · rw [obj_of_not_valid P ha]
    exact ⟨inferInstanceAs (LocallyOfFiniteType (𝟙 _)), inferInstanceAs (QuasiCompact (𝟙 _))⟩

/-- The schemes of the diagram at the models are integral and normal. -/
private theorem isIntegral_isNormal_obj_X (i : ℕ) :
    IsIntegral (obj P (.X i)).left ∧ IsNormal (obj P (.X i)).left := by
  by_cases ha : Valid P (.X i)
  · rw [obj_of_valid P ha]
    exact ⟨inferInstanceAs (IsIntegral (modelSeq X P.Y i)),
      inferInstanceAs (IsNormal (modelSeq X P.Y i))⟩
  · rw [obj_of_not_valid P ha]
    exact ⟨inferInstanceAs (IsIntegral (Spec (.of k))), isNormal_spec_of_isIntegrallyClosed k⟩

end Diagram

/-- **Descent of a countable program.** Let `k` be an algebraically closed field of
characteristic zero and `P` a program from a projective lc pair `(X, B)` over `k`, with
canonical divisor `K`. There are a countable algebraically closed subfield `k₀ ⊆ k`, a pair
`(X₀, B₀)` over `k₀` with canonical divisor `K₀`, and a program `P₀` from it, whose base change
to `k` is `P`: every model `X_i` (`i ≤ n`) is `X_{0,i} ×_{k₀} k` via `πX i`, every target
`Z_i` (`i < n`) is `Z_{0,i} ×_{k₀} k` and the final target `T` is `T₀ ×_{k₀} k`, compatibly
with the contractions `f_i`, the small morphisms `f_i⁺` and the final contraction `g`; the
canonical divisors and the boundaries of `P` are the base changes of those of `P₀`, so the
boundaries carry the same coefficients; the rays of `P` are the images of those of `P₀` under
the base-extension maps `N₁(X_{0,i})_ℝ → N₁(X_i)_ℝ`; and `P` and `P₀` have the same number of
birational steps and both or neither have a final fibre-type ray. -/
@[mmp "prop_oai4_field_transfer_b"]
public theorem Program.exists_countable_isAlgClosed_subfield_program
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {K : Divisor X} {B : QDivisor X} (P : Program sX K B) :
    ∃ (k₀ : Subfield k) (_ : Countable k₀) (_ : IsAlgClosed k₀)
      (X₀ : Scheme.{u}) (_ : IsIntegral X₀) (_ : CompactSpace X₀) (_ : IsLocallyNoetherian X₀)
      (_ : IsNormal X₀) (s₀ : X₀ ⟶ Spec (.of k₀)) (K₀ : Divisor X₀) (B₀ : QDivisor X₀)
      (P₀ : Program s₀ K₀ B₀) (hn : P₀.n = P.n)
      (πX : ∀ i, modelSeq X P.Y i ⟶ modelSeq X₀ P₀.Y i) (πZ : ∀ i, P.Z i ⟶ P₀.Z i)
      (πT : P.T ⟶ P₀.T),
      -- the models are base changes, with divisors `K_i`, `B_i` the base changes
      (∀ i : ℕ, (i : ℕ∞) ≤ P.n →
        IsPullback (πX i) (modelStr sX P.sY i) (modelStr s₀ P₀.sY i)
          (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) ∧
        (∀ (E : MMP.Mori.PrimeDivisor (modelSeq X P.Y i))
            (E₀ : MMP.Mori.PrimeDivisor (modelSeq X₀ P₀.Y i)),
          (πX i).base E.genericPoint = E₀.genericPoint →
            (divisorSeq K P.KY i).coeff E = (divisorSeq K₀ P₀.KY i).coeff E₀ ∧
            (divisorSeq B P.BY i).coeff E = (divisorSeq B₀ P₀.BY i).coeff E₀) ∧
        (∀ E : MMP.Mori.PrimeDivisor (modelSeq X P.Y i),
          (∀ E₀ : MMP.Mori.PrimeDivisor (modelSeq X₀ P₀.Y i),
              (πX i).base E.genericPoint ≠ E₀.genericPoint) →
            (divisorSeq K P.KY i).coeff E = 0 ∧ (divisorSeq B P.BY i).coeff E = 0)) ∧
      -- the steps are base changes, with the rays transported
      (∀ i : ℕ, (i : ℕ∞) < P.n →
        IsPullback (πZ i) (P.sZ i) (P₀.sZ i) (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) ∧
        P.f i ≫ πZ i = πX i ≫ P₀.f i ∧ P.fp i ≫ πZ i = πX (i + 1) ≫ P₀.fp i ∧
        ∀ φ : NumericalCurveClasses (modelStr s₀ P₀.sY i) →ₗ[ℝ]
            NumericalCurveClasses (modelStr sX P.sY i),
          (∀ (C₀ : ProperCurve (modelStr s₀ P₀.sY i)) (C : ProperCurve (modelStr sX P.sY i)),
            closure {C.point} = (πX i).base ⁻¹' closure {C₀.point} →
              φ (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ)) →
          φ '' P₀.R i = P.R i) ∧
      -- the final fibre-type contraction is a base change, with the ray transported
      (P₀.hasFinal ↔ P.hasFinal) ∧
      (P.hasFinal →
        IsPullback πT P.sT P₀.sT (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) ∧
        P.g ≫ πT = πX P.n.toNat ≫
          eqToHom (congrArg (fun m : ℕ∞ => modelSeq X₀ P₀.Y m.toNat) hn.symm) ≫ P₀.g ∧
        ∀ φ : NumericalCurveClasses (modelStr s₀ P₀.sY P₀.n.toNat) →ₗ[ℝ]
            NumericalCurveClasses (modelStr sX P.sY P.n.toNat),
          (∀ (C₀ : ProperCurve (modelStr s₀ P₀.sY P₀.n.toNat))
              (C : ProperCurve (modelStr sX P.sY P.n.toNat)),
            closure {C.point} = (πX P.n.toNat ≫
                eqToHom (congrArg (fun m : ℕ∞ => modelSeq X₀ P₀.Y m.toNat) hn.symm)).base ⁻¹'
                  closure {C₀.point} →
              φ (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ)) →
          φ '' P₀.finalRay = P.finalRay) := by
  classical
  -- the diagram of `P` and its descent to a countable algebraically closed `k₀ ⊆ k`
  let F := diagram P
  haveI := Node.countableCategory (Supp P) P.n
  haveI : ∀ a, LocallyOfFiniteType (F.obj a).hom := fun a => (locallyOfFiniteType_obj P a).1
  haveI : ∀ a, QuasiCompact (F.obj a).hom := fun a => (locallyOfFiniteType_obj P a).2
  have hk₁ : Countable (⊥ : Subfield k) := by
    rw [← Subfield.closure_empty, ← Cardinal.mk_le_aleph0_iff]
    exact (Subfield.cardinalMk_closure_le_max _).trans (max_le (by simp) le_rfl)
  let Pr : ObjectProperty (Node (Supp P) P.n) := fun _ => False
  let g₁ : Spec (.of k) ⟶ Spec (.of (⊥ : Subfield k)) :=
    Spec.map (CommRingCat.ofHom (⊥ : Subfield k).subtype)
  let G : Pr.FullSubcategory ⥤ Over (Spec (.of (⊥ : Subfield k))) :=
    (Functor.const _).obj (Over.mk (𝟙 _))
  let ρ₁ : Pr.ι ⋙ F ⋙ Over.map g₁ ⟶ G :=
    { app := fun j => (show False from j.property).elim
      naturality := fun j => (show False from j.property).elim }
  have hρ₁ : ∀ j, IsPullback (ρ₁.app j).left (F.obj j.obj).hom (G.obj j).hom g₁ :=
    fun j => (show False from j.property).elim
  let σ : PEmpty.{u + 1} → Node (Supp P) P.n := PEmpty.elim
  let M : ∀ s, (F.obj (σ s)).left.Modules := fun s => s.elim
  haveI : ∀ s, (M s).IsQuasicoherent := fun s => s.elim
  haveI : ∀ s, (M s).IsFiniteType := fun s => s.elim
  let Q : PEmpty.{u + 1} → Prop := fun _ => False
  have hQ : ∀ s, Q s → Pr (σ s) := fun s => s.elim
  let M₁ : ∀ s (hs : Q s), (G.obj ⟨σ s, hQ s hs⟩).left.Modules := fun s => s.elim
  haveI : ∀ s (hs : Q s), (M₁ s hs).IsQuasicoherent := fun s => s.elim
  haveI : ∀ s (hs : Q s), (M₁ s hs).IsFiniteType := fun s => s.elim
  obtain ⟨k₀, hc, ha, -, F₀, π, -, -, -, -, -, -, hft, hpb, -⟩ :=
    MMP.FieldOfDefinition.exists_countable_isAlgClosed_model F σ M (H := PEmpty.{u + 1})
      PEmpty.elim PEmpty.elim (fun h => h.elim) (fun h => h.elim) ⊥ Pr G ρ₁ hρ₁ Q hQ M₁
      (fun s => s.elim)
  set g₀ : Spec (.of k) ⟶ Spec (.of k₀) := Spec.map (CommRingCat.ofHom (algebraMap k₀ k))
  have hpb' : ∀ a, IsPullback (π.app a).left (obj P a).hom (F₀.obj a).hom g₀ := hpb
  haveI : ∀ a, LocallyOfFiniteType (F₀.obj a).hom := fun a => (hft a).1
  haveI : ∀ a, QuasiCompact (F₀.obj a).hom := fun a => (hft a).2
  -- the comparison maps `p a : real a ⟶ F₀ a`
  let p : ∀ a : Node (Supp P) P.n, (real P a).left ⟶ (F₀.obj a).left :=
    fun a => (toObj P a).left ≫ (π.app a).left
  have hp_pb : ∀ a, Valid P a → IsPullback (p a) (real P a).hom (F₀.obj a).hom g₀ := by
    intro a ha
    simp only [p, toObj_of_valid P ha]
    exact isPullback_eqToHom_left_comp _ (hpb' a)
  have hp_nat : ∀ (a b : Node (Supp P) P.n) (h : a ⟶ b) (hs : Node.Step a b) (hb : Valid P b),
      (realMap P a b hs hb).left ≫ p b = p a ≫ (F₀.map h).left := by
    intro a b h hs hb
    have h1 := congrArg CommaMorphism.left (π.naturality h)
    have h2 := congrArg CommaMorphism.left (toObj_comp_diagram_map P h hs hb)
    calc (realMap P a b hs hb).left ≫ p b
        = (realMap P a b hs hb ≫ toObj P b).left ≫ (π.app b).left :=
          (Category.assoc _ _ _).symm
      _ = (toObj P a ≫ (diagram P).map h).left ≫ (π.app b).left :=
          congrArg (· ≫ (π.app b).left) h2.symm
      _ = (toObj P a).left ≫ ((F.map h).left ≫ (π.app b).left) := Category.assoc _ _ _
      _ = (toObj P a).left ≫ ((π.app a).left ≫ (F₀.map h).left) := congrArg _ h1
      _ = p a ≫ (F₀.map h).left := (Category.assoc _ _ _).symm
  -- the descended models are integral, normal, compact and locally Noetherian
  have hXinst : ∀ i, IsIntegral (F₀.obj (.X i)).left ∧ IsNormal (F₀.obj (.X i)).left ∧
      CompactSpace (F₀.obj (.X i)).left ∧ IsLocallyNoetherian (F₀.obj (.X i)).left := by
    intro i
    obtain ⟨hnor, hint, -⟩ :=
      MMP.ProgramBaseChange.invariants_of_isPullback (F₀.obj (.X i)).hom (hpb' (.X i))
    obtain ⟨h1, h2⟩ := isIntegral_isNormal_obj_X P i
    exact ⟨hint.2 h1, hnor.2 h2, QuasiCompact.compactSpace_of_compactSpace (F₀.obj (.X i)).hom,
      LocallyOfFiniteType.isLocallyNoetherian (F₀.obj (.X i)).hom⟩
  -- the descended data
  let GX : ℕ → Scheme.{u} := fun i => (F₀.obj (.X i)).left
  haveI : ∀ i, IsIntegral (GX i) := fun i => (hXinst i).1
  haveI : ∀ i, IsNormal (GX i) := fun i => (hXinst i).2.1
  haveI : ∀ i, CompactSpace (GX i) := fun i => (hXinst i).2.2.1
  haveI : ∀ i, IsLocallyNoetherian (GX i) := fun i => (hXinst i).2.2.2
  let s₀ : GX 0 ⟶ Spec (.of k₀) := (F₀.obj (.X 0)).hom
  let Y₀ : ℕ → Scheme.{u} := fun i => GX (i + 1)
  let sY₀ : ∀ i, Y₀ i ⟶ Spec (.of k₀) := fun i => (F₀.obj (.X (i + 1))).hom
  let ι := modelSeqIso GX
  have hstr : ∀ i, (ι i).hom ≫ (F₀.obj (.X i)).hom = modelStr s₀ sY₀ i :=
    modelSeqIso_hom_comp_hom (fun i => F₀.obj (.X i))
  let πX : ∀ i, modelSeq X P.Y i ⟶ modelSeq (GX 0) Y₀ i := fun i => p (.X i) ≫ (ι i).inv
  let Z₀ : ℕ → Scheme.{u} := fun i => (F₀.obj (.Z i)).left
  let sZ₀ : ∀ i, Z₀ i ⟶ Spec (.of k₀) := fun i => (F₀.obj (.Z i)).hom
  let πZ : ∀ i, P.Z i ⟶ Z₀ i := fun i => p (.Z i)
  let hXZ : ∀ i, (Node.X i : Node (Supp P) P.n) ⟶ .Z i := fun i => homOfLE (Or.inr (Or.inl rfl))
  let hXsZ : ∀ i, (Node.X (i + 1) : Node (Supp P) P.n) ⟶ .Z i :=
    fun i => homOfLE (Or.inr (Or.inr rfl))
  let hXT : (Node.X P.n.toNat : Node (Supp P) P.n) ⟶ .T := homOfLE (Or.inr rfl)
  let f₀ : ∀ i, modelSeq (GX 0) Y₀ i ⟶ Z₀ i := fun i => (ι i).hom ≫ (F₀.map (hXZ i)).left
  let fp₀ : ∀ i, Y₀ i ⟶ Z₀ i := fun i => (F₀.map (hXsZ i)).left
  let gT₀ : modelSeq (GX 0) Y₀ P.n.toNat ⟶ (F₀.obj .T).left :=
    (ι P.n.toNat).hom ≫ (F₀.map hXT).left
  -- base change squares and compatibilities
  have hπX : ∀ i : ℕ, (i : ℕ∞) ≤ P.n →
      IsPullback (πX i) (modelStr sX P.sY i) (modelStr s₀ sY₀ i) g₀ := by
    intro i hi
    rw [← hstr i]
    exact isPullback_comp_inv (hp_pb (.X i) hi) (ι i)
  have hπZ : ∀ i : ℕ, (i : ℕ∞) < P.n → IsPullback (πZ i) (P.sZ i) (sZ₀ i) g₀ :=
    fun i hi => hp_pb (.Z i) hi
  have hπT : P.hasFinal → IsPullback (p .T) P.sT (F₀.obj .T).hom g₀ :=
    fun h => hp_pb .T h
  have hfπ : ∀ i : ℕ, (i : ℕ∞) < P.n → P.f i ≫ πZ i = πX i ≫ f₀ i := by
    intro i hi
    have h1 : P.f i ≫ p (.Z i) = p (.X i) ≫ (F₀.map (hXZ i)).left := by
      rw [← realMap_X_Z P i (Or.inl rfl) hi]
      exact hp_nat (.X i) (.Z i) (hXZ i) (Or.inl rfl) hi
    refine h1.trans ?_
    show _ = (p (.X i) ≫ (ι i).inv) ≫ (ι i).hom ≫ (F₀.map (hXZ i)).left
    rw [Category.assoc, Iso.inv_hom_id_assoc]
  have hfpπ : ∀ i : ℕ, (i : ℕ∞) < P.n → P.fp i ≫ πZ i = πX (i + 1) ≫ fp₀ i := by
    intro i hi
    have h1 : P.fp i ≫ p (.Z i) = p (.X (i + 1)) ≫ (F₀.map (hXsZ i)).left := by
      rw [← realMap_X_succ_Z P i (Or.inr rfl) hi]
      exact hp_nat (.X (i + 1)) (.Z i) (hXsZ i) (Or.inr rfl) hi
    refine h1.trans ?_
    show _ = (p (.X (i + 1)) ≫ 𝟙 _) ≫ (F₀.map (hXsZ i)).left
    rw [Category.comp_id]
  have hgπ : P.hasFinal → P.g ≫ p .T = πX P.n.toNat ≫ gT₀ := by
    intro h
    have h1 : P.g ≫ p .T = p (.X P.n.toNat) ≫ (F₀.map hXT).left := by
      rw [← realMap_X_T P rfl h]
      exact hp_nat (.X P.n.toNat) .T hXT rfl h
    refine h1.trans ?_
    show _ = (p (.X P.n.toNat) ≫ (ι P.n.toNat).inv) ≫ (ι P.n.toNat).hom ≫ (F₀.map hXT).left
    rw [Category.assoc, Iso.inv_hom_id_assoc]
  have hf₀ : ∀ i : ℕ, (i : ℕ∞) < P.n → f₀ i ≫ sZ₀ i = modelStr s₀ sY₀ i := by
    intro i _
    simp only [f₀, sZ₀, Category.assoc, Over.w, hstr]
  have hfp₀ : ∀ i : ℕ, (i : ℕ∞) < P.n → fp₀ i ≫ sZ₀ i = sY₀ i := fun i _ => Over.w _
  have hg₀ : P.hasFinal → gT₀ ≫ (F₀.obj .T).hom = modelStr s₀ sY₀ P.n.toNat := by
    intro _
    simp only [gT₀, Category.assoc, Over.w, hstr]
  haveI : ∀ i, IsIntegral (Y₀ i) := fun i => (hXinst (i + 1)).1
  haveI : ∀ i, IsNormal (Y₀ i) := fun i => (hXinst (i + 1)).2.1
  haveI : ∀ i, CompactSpace (Y₀ i) := fun i => (hXinst (i + 1)).2.2.1
  haveI : ∀ i, IsLocallyNoetherian (Y₀ i) := fun i => (hXinst (i + 1)).2.2.2
  haveI : ∀ i, LocallyOfFiniteType (modelStr s₀ sY₀ i) := fun i => by
    rw [← hstr i]
    infer_instance
  have hsurj : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → Surjective (πX i) :=
    fun i hi => MMP.ProgramBaseChange.surjective_of_isPullback (hπX i hi)
  have hproj : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → MMP.Mori.IsProjectiveVariety k₀ (modelStr s₀ sY₀ i) :=
    fun i hi => (MMP.ProgramBaseChange.isProjectiveVariety_iff_of_isPullback _ _ _ (hπX i hi)).2
      (isProjectiveVariety_model P hi)
  -- the support primes of `K_i` and `B_i` are base changes of prime divisors over `k₀`
  have hsupp : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∀ E ∈ suppPrimes P i,
      ∃ E₀ : MMP.Mori.PrimeDivisor (modelSeq (GX 0) Y₀ i),
        closure {E.genericPoint} = (πX i).base ⁻¹' closure {E₀.genericPoint} := by
    intro i hi E hE
    haveI := hsurj i hi
    let hXX' : (Node.X i : Node (Supp P) P.n) ⟶ .X' i := homOfLE (Or.inr rfl)
    let hDX' : (Node.D i ⟨E, hE⟩ : Node (Supp P) P.n) ⟶ .X' i := homOfLE (Or.inr rfl)
    have sXX' : Node.Step (Node.X i : Node (Supp P) P.n) (.X' i) := rfl
    have sDX' : Node.Step (Node.D i ⟨E, hE⟩ : Node (Supp P) P.n) (.X' i) := rfl
    have hX' : p (.X' i) = πX i ≫ ((ι i).hom ≫ (F₀.map hXX').left) := by
      have h1 := hp_nat (.X i) (.X' i) hXX' sXX' hi
      rw [realMap_X_X'_comp P i sXX' hi] at h1
      rw [h1]
      show _ = (p (.X i) ≫ (ι i).inv) ≫ (ι i).hom ≫ (F₀.map hXX').left
      rw [Category.assoc, Iso.inv_hom_id_assoc]
    have hsq : IsPullback E.idealSheaf.subschemeι (p (.D i ⟨E, hE⟩)) (p (.X' i))
        (F₀.map hDX').left := by
      refine IsPullback.of_right (h₁₂ := modelStr sX P.sY i) (v₁₃ := g₀)
        (h₂₂ := (F₀.obj (.X' i)).hom) ?_ ?_ (hp_pb (.X' i) hi).flip
      · rw [Over.w (F₀.map hDX')]
        exact (hp_pb (.D i ⟨E, hE⟩) hi).flip
      · rw [← realMap_D_X' P i ⟨E, hE⟩ sDX' hi]
        exact hp_nat _ _ hDX' sDX' hi
    rw [hX'] at hsq
    exact exists_closure_eq_of_isPullback_subschemeι (hπX i hi) _ E hsq
  -- the descended divisors
  let K₀ : Divisor (GX 0) := descendDivisor (πX 0) K
  let KY₀ : ∀ i, Divisor (Y₀ i) := fun i => descendDivisor (πX (i + 1)) (P.KY i)
  let B₀ : QDivisor (GX 0) := descendDivisor (πX 0) B
  let BY₀ : ∀ i, QDivisor (Y₀ i) := fun i => descendDivisor (πX (i + 1)) (P.BY i)
  have hdivK : ∀ i, divisorSeq K₀ KY₀ i = descendDivisor (πX i) (divisorSeq K P.KY i) :=
    fun i => by cases i <;> rfl
  have hdivB : ∀ i, divisorSeq B₀ BY₀ i = descendDivisor (πX i) (divisorSeq B P.BY i) :=
    fun i => by cases i <;> rfl
  have hKB : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∀ (E₀ : MMP.Mori.PrimeDivisor (modelSeq (GX 0) Y₀ i))
      (E : MMP.Mori.PrimeDivisor (modelSeq X P.Y i)),
      closure {E.genericPoint} = (πX i).base ⁻¹' closure {E₀.genericPoint} →
        divisorSeq K P.KY i E = divisorSeq K₀ KY₀ i E₀ ∧
          divisorSeq B P.BY i E = divisorSeq B₀ BY₀ i E₀ := by
    intro i hi E₀ E h
    haveI := hsurj i hi
    rw [hdivK, hdivB, descendDivisor_apply _ _ h, descendDivisor_apply _ _ h]
    exact ⟨rfl, rfl⟩
  have hKBsupp : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∀ E : MMP.Mori.PrimeDivisor (modelSeq X P.Y i),
      (divisorSeq K P.KY i E ≠ 0 ∨ divisorSeq B P.BY i E ≠ 0) →
        ∃ E₀ : MMP.Mori.PrimeDivisor (modelSeq (GX 0) Y₀ i),
          closure {E.genericPoint} = (πX i).base ⁻¹' closure {E₀.genericPoint} := by
    intro i hi E hE
    exact hsupp i hi E (by simpa only [suppPrimes, Finset.mem_union, Finsupp.mem_support_iff])
  -- the rays, through the base-extension maps of curve classes
  let e : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → NumericalCurveClasses (modelStr s₀ sY₀ i) ≃ₗ[ℝ]
      NumericalCurveClasses (modelStr sX P.sY i) :=
    fun i hi => numericalCurveClassesBaseChange _ _ _ (hπX i hi) (hproj i hi)
  have he : ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ P.n) (C₀ : ProperCurve (modelStr s₀ sY₀ i))
      (C : ProperCurve (modelStr sX P.sY i)),
      closure {C.point} = (πX i).base ⁻¹' closure {C₀.point} →
        e i hi (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ) :=
    fun i hi => numericalCurveClassesBaseChange_eq_of_isPullback _ _ _ (hπX i hi) (hproj i hi)
  clear_value e
  let φ : ∀ i, NumericalCurveClasses (modelStr s₀ sY₀ i) →ₗ[ℝ]
      NumericalCurveClasses (modelStr sX P.sY i) :=
    fun i => if h : (i : ℕ∞) ≤ P.n then (e i h).toLinearMap else 0
  have hφ_eq : ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ P.n), φ i = (e i hi).toLinearMap := fun i hi => dif_pos hi
  have hφ : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∀ (C₀ : ProperCurve (modelStr s₀ sY₀ i))
      (C : ProperCurve (modelStr sX P.sY i)),
      closure {C.point} = (πX i).base ⁻¹' closure {C₀.point} →
        φ i (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ) :=
    fun i hi C₀ C h => (LinearMap.congr_fun (hφ_eq i hi) _).trans (he i hi C₀ C h)
  have huniq : ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ P.n) (ψ : NumericalCurveClasses (modelStr s₀ sY₀ i) →ₗ[ℝ]
      NumericalCurveClasses (modelStr sX P.sY i)),
      (∀ (C₀ : ProperCurve (modelStr s₀ sY₀ i)) (C : ProperCurve (modelStr sX P.sY i)),
        closure {C.point} = (πX i).base ⁻¹' closure {C₀.point} →
          ψ (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ)) →
      ψ = (e i hi).toLinearMap :=
    fun i hi ψ hψ => eq_of_forall_closure_eq (hπX i hi) hψ (he i hi)
  have himage : ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ P.n)
      (S : Set (NumericalCurveClasses (modelStr sX P.sY i))),
      (e i hi).toLinearMap '' ((e i hi).symm '' S) = S := fun i hi S => by
    simp only [LinearEquiv.coe_coe]
    exact (e i hi).toEquiv.image_symm_image S
  have hsubcone : ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ P.n)
      (S : Set (NumericalCurveClasses (modelStr sX P.sY i))),
      S ⊆ closedConeOfCurves (modelStr sX P.sY i) →
        (e i hi).symm '' S ⊆ closedConeOfCurves (modelStr s₀ sY₀ i) :=
    fun i hi S => symm_image_subset_of_map_eq (e i hi)
      (map_closedConeOfCurves_eq_of_isPullback _ _ _ (hπX i hi) (hproj i hi) _ (he i hi))
  let R₀ : ∀ i, Set (NumericalCurveClasses (modelStr s₀ sY₀ i)) :=
    fun i => if h : (i : ℕ∞) ≤ P.n then (e i h).symm '' P.R i else ∅
  have hR₀_eq : ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ P.n), R₀ i = (e i hi).symm '' P.R i :=
    fun i hi => dif_pos hi
  have hnle : (P.n.toNat : ℕ∞) ≤ P.n := ENat.coe_toNat_le_self P.n
  let finalRay₀ := (e _ hnle).symm '' P.finalRay
  have hR : ∀ i : ℕ, (i : ℕ∞) < P.n → P.R i = φ i '' R₀ i := fun i hi => by
    rw [hφ_eq i hi.le, hR₀_eq i hi.le, himage]
  have hfinal : P.hasFinal → P.finalRay = φ P.n.toNat '' finalRay₀ := fun _ => by
    rw [hφ_eq _ hnle, himage]
  have hR₀ : ∀ i : ℕ, (i : ℕ∞) < P.n → R₀ i ⊆ closedConeOfCurves (modelStr s₀ sY₀ i) := by
    intro i hi
    obtain ⟨_, hray, _⟩ := (P.isPermittedStep i hi).isNegativeExtremalRayOf
    rw [hR₀_eq i hi.le]
    exact hsubcone i hi.le _ hray.1.1
  have hfinal₀ : P.hasFinal → finalRay₀ ⊆ closedConeOfCurves (modelStr s₀ sY₀ P.n.toNat) := by
    intro h
    obtain ⟨_, hray, _⟩ := (P.final_spec h).2.1
    exact hsubcone _ hnle _ hray.1.1
  -- the descended data form a program
  have hf : ∀ i : ℕ, (i : ℕ∞) < P.n → P.f i ≫ P.sZ i = modelStr sX P.sY i :=
    fun i hi => (P.isPermittedStep i hi).isContractionOfRay.comp_eq
  have hfp : ∀ i : ℕ, (i : ℕ∞) < P.n → P.fp i ≫ P.sZ i = P.sY i :=
    fun i hi => (P.isPermittedStep i hi).isSmallMorphism_step.comp_eq
  have hg : P.hasFinal → P.g ≫ P.sT = modelStr sX P.sY P.n.toNat :=
    fun h => (P.final_spec h).2.2.1.comp_eq
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    (program_conditions_iff_of_isPullback (k₀ := k₀) (K := k) P.n P.hasFinal s₀ K₀ B₀ sY₀ KY₀
      BY₀ R₀ hR₀ sZ₀ f₀ hf₀ fp₀ hfp₀ finalRay₀ hfinal₀ (F₀.obj .T).hom gT₀ hg₀ sX K B P.sY P.KY
      P.BY P.R P.sZ P.f hf P.fp hfp P.finalRay P.sT P.g hg πX hπX πZ hπZ (p .T) hπT hfπ hfpπ hgπ
      hKB hKBsupp φ hφ hR hfinal).2
      ⟨P.isProjectiveVariety, P.isLogCanonicalPair, P.isCanonicalDivisor, P.isPermittedStep,
        P.KY_eq, P.BY_eq, P.final_spec⟩
  let P₀ : Program s₀ K₀ B₀ :=
    { n := P.n, Y := Y₀, sY := sY₀, KY := KY₀, BY := BY₀, R := R₀, Z := Z₀, sZ := sZ₀,
      f := f₀, fp := fp₀, isProjectiveVariety := h1, isLogCanonicalPair := h2,
      isCanonicalDivisor := h3, isPermittedStep := h4, KY_eq := h5, BY_eq := h6,
      hasFinal := P.hasFinal, finalRay := finalRay₀, T := (F₀.obj .T).left,
      sT := (F₀.obj .T).hom, g := gT₀, final_spec := h7 }
  refine ⟨k₀, hc, ha, GX 0, inferInstance, inferInstance, inferInstance, inferInstance, s₀, K₀,
    B₀, P₀, rfl, πX, πZ, p .T, ?_, ?_, Iff.rfl, ?_⟩
  · -- the models and their divisors
    intro i hi
    haveI := hsurj i hi
    refine ⟨hπX i hi, ?_, ?_⟩
    · intro E E₀ hE
      obtain ⟨E₀', hE₀'⟩ := exists_closure_eq_of_map_ne_genericPoint (hπX i hi) E
        (by rw [hE]; exact genericPoint_ne_genericPoint E₀)
      have : E₀' = E₀ := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((MMP.ProgramBaseChange.map_eq_of_closure_eq hE₀').symm.trans hE)
      subst this
      exact hKB i hi E₀' E hE₀'
    · intro E hE
      by_contra hne
      rw [not_and_or] at hne
      obtain ⟨E₀, h⟩ := hKBsupp i hi E hne
      exact hE E₀ (MMP.ProgramBaseChange.map_eq_of_closure_eq h)
  · -- the steps and their rays
    intro i hi
    refine ⟨hπZ i hi, hfπ i hi, hfpπ i hi, fun ψ hψ => ?_⟩
    change ψ '' R₀ i = P.R i
    rw [huniq i hi.le ψ hψ, hR₀_eq i hi.le, himage]
  · -- the final contraction and its ray
    intro h
    refine ⟨hπT h, ?_, fun ψ hψ => ?_⟩
    · simpa using hgπ h
    · simp only [eqToHom_refl, Category.comp_id] at hψ
      change ψ '' finalRay₀ = P.finalRay
      rw [huniq _ hnle ψ hψ, himage]

end MMP.Fourfold
